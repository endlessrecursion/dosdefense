package com.kryptowire.dosdefense;

import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Date;
import java.util.GregorianCalendar;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Scanner;
import android.app.AlarmManager;
import android.app.PendingIntent;
import android.content.Context;
import android.content.Intent;
import android.hardware.Camera;
import android.media.MediaRecorder;
import android.os.RemoteException;
import android.util.Log;
import de.robv.android.xposed.IXposedHookLoadPackage;
import de.robv.android.xposed.XC_MethodHook;
import de.robv.android.xposed.XC_MethodHook.MethodHookParam;
import de.robv.android.xposed.callbacks.XC_LoadPackage.LoadPackageParam;
import static de.robv.android.xposed.XposedHelpers.findAndHookMethod;

/* This Xposed Module requires that you have Xposed installed on the device. The module will guard 
 * against certain DoS attacks such as making the device unresponsive, killing other applications,
 * soft rebooting the device, monopolizing the microphone resource, and monopolizing the camera 
 * resource. The majority of the code is to rate-limit the sending of intents by an application. 
 * Thresholds are set over a short and long time interval to track and limit the intent usage. The
 * application will be limited by these thresholds and any subsequent intents will not be sent until
 * the time intervals reset and allow the application to send intents again. The application can send
 * a maximum of INTENT_MAX_COUNT_SHORT intents every SHORT_PERIOD_SECS seconds. In addition, the app 
 * can send a maximum of INTENT_MAX_COUNT_LONG intents every LONG_PERIOD_SECS seconds. If the app tries
 * to send more intents than the threshold allows, these "extra" intents will not be sent. If the app 
 * attempts to send more than INTENT_MAX_COUNT_KILL_LONG intents during the a LONG_PERIOD_SECS time 
 * window, then the app will be killed. The module will also prevent recording to /dev/null when using
 * the android.media.MediaRecorder to record audio and video. This prevents an app from monopolizing the
 * microphone resource for an indefinite period of time. When an app opens or locks the camera, they
 * will have time limits through moving the regular stages of using the camera. Otherwise, the camera
 * will be released from the application that is not making progress within the time limits. Once an app
 * opens the camera they will have MOVE_FROM_OPEN seconds to move to another stage. They can progress 
 * backwards to a earlier stage but this will not reset the timer to progress forward to a new stage. 
 * The timer cannot be reset by calling the same stage over again except for taking pictures. An app 
 * or user can take pictures over and over again, but they will have MOVE_FROM_TAKEPICTURE seconds to 
 * take another picture or release the camera after they take each picture. The takePicture stage can 
 * move back to the openPreview step since this occurs after taking a picture. The progression goes 
 * Camera.open(...) -> Camera.lock() -> Camera.openPreview() -> Camera.takPicture(...) -> 
 * Camera.release(). Different stages can be skipped in the progression but forward progress through 
 * the stages must be made within the time limit. Otherwise, the camera will be released from the 
 * application so they cannot maintain exclusive control over the camera. 
 * If KILL_APP_THAT_DOES_NOT_PROGRESS_ON_CAMERA is true, then an app will also be killed after the 
 * camera is forcibly released.
 */

public class DoSDefenseModule implements IXposedHookLoadPackage {

	private final static HashSet<String> exclusionList =  new HashSet<String>(); // a hash set of strings containing the package names of apps that should not be subjected to this module
	private final static String TAG = DoSDefenseModule.class.getName(); // log tag for writing to the Android log
	private Hashtable<String, IntentFreqContainer> intentDataPerApp = new Hashtable<String, IntentFreqContainer>(); // stores the intent usage per app
	private static final long SHORT_PERIOD_SECS = 10; // the number of seconds for the short time period
	private static final long LONG_PERIOD_SECS = 120; // the number of seconds for the long time period
	private static final int INTENT_MAX_COUNT_SHORT = 15; // the maximum number of intents that can be sent in the short time period
	private static final int INTENT_MAX_COUNT_LONG = 70; // the maximum number of intents that can be sent in the log time period
	private static final int INTENT_MAX_COUNT_KILL_LONG = 300; // the number of intents sent in long time period that will prevent the app from sending more intents	
	private static final int NEW_TASK_INTENT_WEIGHT = 4; // the weight of intents that use the FLAG_ACTIVITY_NEW_TASK Intent flag	
	private static final boolean DEBUG = true; // if true, write debugging information to the log	
	private static boolean killThisApp = false; // if true, this app should be killed since it sent to many intents
	private static GregorianCalendar cameraOpenTS = null; // a timestamp for when Camera.lock() is called
	private static GregorianCalendar cameraLockTS = null; // a timestamp for when Camera.lock() is called
	private static GregorianCalendar cameraOpenPreviewTS = null; // a timestamp for when Camera.startPreview() is called
	private static GregorianCalendar cameraTakePictureTS = null; // a timestamp for when Camera.takePicture(...) is called	
	private static CameraWatchdog camWatchdog; // a thread to keep track of the progression of the camera usage
	private static Camera cam; // a reference to the open camera, so it can be released if needed
	private final static boolean EXCLUDE_MOST_SYSTEM_APPS = false; // a boolean whether or not to use a whitelist of system apps that should not be subjected to this module
	private static Boolean isExcluded = null; // a boolean to denote if the app that the Xposed module is injected to is in the exclusion list
	private static final int INTENT_VALUE_RETURN = 1; // the value to return when intents are being sent too quickly
	private static final boolean KILL_APP_THAT_DOES_NOT_PROGRESS_ON_CAMERA = true; // if true, the  app will be killed except the system camera app 
	private static Context appContext = null; // the context of the application
	private static final boolean REMOVE_PENDING_INTENTS_FROM_ALARM_MANAGER = true; // if true, then remove the PendingIntents sent via AlarmManager if they are too aggressive
	private static final int MOVE_FROM_OPEN = 30; // number of seconds an app can call Camera.open(...) without progressing
	private static final int MOVE_FROM_LOCK = 45; // number of seconds an app can call Camera.lock() without progressing
	private static final int MOVE_FROM_STARTPREVIEW = 60; // the number of seconds an app can call Camera.startPreview() without progressing
	private static final int MOVE_FROM_TAKEPICTURE = 70; // the number of seconds an app can call Camera.takePicture() without releasing the camera or taking another picture
	private static final String CAM_FREE_STAGE = "free"; // the stage of the camera being free
	private static final String CAM_OPEN_STAGE = "open"; // the stage of the camera being open
	private static final String CAM_LOCK_STAGE = "lock"; // the stage of the camera being locked
	private static final String CAM_STARTPREVIEW_STAGE = "startPreview"; // the stage of the camera being in startPreview
	private static final String CAM_TAKEPICTURE_STAGE = "takePicture"; // the stage of the camera being in takePicture	
	private static String currentCameraStage = CAM_FREE_STAGE; // the current stage of the camera
	
	public DoSDefenseModule() {}
	
	// will add the package names of system apps on the device to the exclusionList except for the android 
	// and com.android.providers.settings packages
    private void getSystemApps() {
    	ProcessBuilder builder = new ProcessBuilder("pm", "list", "packages", "-s");
    	Process process = null;
    	Scanner scanner = null;
		try {
			process = builder.start();
	    	InputStream in = process.getInputStream();
	    	scanner = new Scanner(in);
	    	while (scanner.hasNext()) {
	    		String line = scanner.next();
	    		if (line.startsWith("package:")) {
	    			String packageName = line.substring(8);	    			
	    			if (!packageName.equals("android") && !packageName.equals("com.android.providers.settings")) {
	    				exclusionList.add(packageName);	
	    			}
	    		}
	    	}
		} catch (IOException e) {
			e.printStackTrace();
			if (DEBUG)
				Log.d(TAG, "IOException in getSystemApps");
			return;
		}
		finally {
			if (scanner != null)
				scanner.close();
			if (process != null)
				process.destroy();
		}
    }
	
    // class to store intent data for an app
	public static class IntentFreqContainer {
		long initialTimeStamp; // initial time stamp (when app started)
		long shortTimestamp; // a timestamp for the when short time interval started
		long longTimestamp; // a timestamp for the when long time interval started
		int numIntentsSentShort; // number of intents sent during the short interval
		int numIntentsSentLong; // number of intents sent during the long interval
				
		IntentFreqContainer(long nanoTime, int numInitialIntents) {
			this.shortTimestamp = nanoTime;
			this.initialTimeStamp = nanoTime;
			this.longTimestamp = nanoTime;
			this.numIntentsSentShort = numInitialIntents;
			this.numIntentsSentLong = numInitialIntents;
		}
		
		// resets the intents sent for the short time interval and updates the timestamp for the short time interval
		void updateShortTimeAndResetNumTimes(long newTime) {
			this.shortTimestamp = newTime;
			this.numIntentsSentShort = 0;
		}		
		
		// resets the intents sent for the long time interval and updates the timestamp for the long time interval
		void updateLongTimeAndResetNumTimes(long newTime) {
			this.longTimestamp = newTime;
			this.numIntentsSentLong = 0;
		}
		
		// increments the number of intents sent by the app
		void addIntentsSent(int numIntents) {
			this.numIntentsSentShort += numIntents;
			this.numIntentsSentLong += numIntents;			
		}		
	}
	
	// this method will try to obtain and return an instance field from an object by name
	private Object tryToGetObjectFieldUsingReflection(String fieldName, Object obj) {
		Object getit = null;
		Field field = null;
		if (obj == null)
			return null;
		Class<?> aClass = obj.getClass();
		boolean found = false;
		while (aClass != null && found == false) {
			try {
				field = aClass.getDeclaredField(fieldName);
				field.setAccessible(true);
				found = true;
			} catch (SecurityException e) {
				return getit;
			} catch (NoSuchFieldException e) {
				// the field may be present in a superclass
				aClass = aClass.getSuperclass();
			}					
		}
		if (field != null) {
			try {
				getit = field.get(obj);
			} catch (IllegalArgumentException e) {
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			}
		}				
		return getit;
	}
	
	// this method will return true if the app is sending intents higher than the short and/or long threshold for intent usage
	private boolean isRateTooFast(String callingPackage, int intentsCount) throws RemoteException {
		long currentNano = System.nanoTime(); // get the current time
		IntentFreqContainer ifc = intentDataPerApp.get(callingPackage); // try to obtain the entry from the hash table
		if (ifc != null) { 
			// app has sent intents before
			double shortDeltaSecs = (double) ((currentNano - ifc.shortTimestamp) / 1e9); // the time between current time and the last short timestamp in seconds as a double
			double longDeltaSecs = (double) ((currentNano - ifc.longTimestamp ) / 1e9); // the time between current time and the last long timestamp in seconds as a double
			
			// general debug info
			if (DEBUG)
				Log.d(TAG, "[" + callingPackage + "] : short time delta [" + shortDeltaSecs + "] - number of intents in short time period [" + ifc.numIntentsSentShort + "] - long time delta [" + longDeltaSecs + "] - number of intents in long time period [" + ifc.numIntentsSentLong + "]");
			
			if (DoSDefenseModule.killThisApp) {
				// the app has too many intents and must die
				if (DEBUG)
					Log.d(TAG, "[" + callingPackage + "] : killing app!");
				android.os.Process.killProcess(android.os.Process.myPid());
				return true;
			}
			
			// update the timestamps if necessary
			if (longDeltaSecs >= LONG_PERIOD_SECS)
				ifc.updateLongTimeAndResetNumTimes(currentNano);
			if (shortDeltaSecs >= SHORT_PERIOD_SECS)
				ifc.updateShortTimeAndResetNumTimes(currentNano);	

			// add the number of intents that the process is trying to send
			ifc.addIntentsSent(intentsCount); 
				
			// check if the intents sent over the longer time interval have been exceeded
			if (ifc.numIntentsSentLong > INTENT_MAX_COUNT_LONG) {
				if (DEBUG)
					Log.d(TAG, "[" + callingPackage +"] attempted to send " + ifc.numIntentsSentLong + " which is more than " + INTENT_MAX_COUNT_LONG + " per long period");
				if (ifc.numIntentsSentLong > INTENT_MAX_COUNT_KILL_LONG) {
					// let's not kill android which will soft reboot the system
					if (!callingPackage.equals("android") && !callingPackage.equals("com.android.providers.settings")) {
						if (DEBUG)
							Log.d(TAG, "[" + callingPackage + "] : killing app! - attempted to send " + ifc.numIntentsSentLong + " intents in " + longDeltaSecs + " seconds which is more than the max threshold of " + INTENT_MAX_COUNT_KILL_LONG);
						DoSDefenseModule.killThisApp = true;
						android.os.Process.killProcess(android.os.Process.myPid());						
					}
				}
				return true;
			}			
			
			// check if the intents sent over the shorter time interval have been exceeded
			if (ifc.numIntentsSentShort > INTENT_MAX_COUNT_SHORT) {
				if (DEBUG)
					Log.d(TAG, "[" + callingPackage +"] attempted to send " + ifc.numIntentsSentShort + " which is more than " + INTENT_MAX_COUNT_SHORT + " per short period");
				return true;
			}			
			return false;
		}
		else { 
			// this is the first time that the app has sent an intent
			ifc = new IntentFreqContainer(currentNano, intentsCount);
			intentDataPerApp.put(callingPackage, ifc);			
			if (DEBUG)
				Log.d(TAG, "[" + callingPackage + "] added to hashtable - " + currentNano);
			
			// check if they are sending more than the max on their first sending on an intent (e.g., sending 400 intents using startActivities(Intent[]))
			if (ifc.numIntentsSentShort > INTENT_MAX_COUNT_SHORT) {
				if (DEBUG)
					Log.d(TAG, "[" + callingPackage +"] attempted to send " + ifc.numIntentsSentShort + " which is more than " + INTENT_MAX_COUNT_SHORT + " per short period");
				return true;
			}
			return false;
		}
	}
	
	// will return true is bit x is set in the integer value. Otherwise, it will return false
	private static boolean isBitSet(int value, int x) {		
		if ((value & (1L << x)) != 0) {
			return true;
		}
		return false;
	}
	
	// Returns true if the parameter is an intent with the FLAG_ACTIVITY_MULTIPLE_TASK flag set 
	private static boolean willIntentCreateNewTask(Object i) {
		if (i == null)
			return false;
		try {
			Intent intent = (Intent) i;
			int flags = intent.getFlags();
			boolean ret = DoSDefenseModule.isBitSet(flags, 27);
			if (DEBUG)
				Log.d(TAG, "the flags " + flags + " will create a new task - " + ret);
			return ret;			
		}
		catch (ClassCastException e) {
			return false;
		}
	}
	
	// this method will return true if the app is making forward progress when using
	// the camera
	private static boolean isForwardProgress(String currentStage, String nextStage) {
		
		if (currentStage.equals(CAM_FREE_STAGE) || nextStage.equals(CAM_FREE_STAGE)) {
			// if the camera is currently free any other stage is progress or if they move to it being free then
			// the cycle is complete
			return true;
		}
		else if (nextStage.equals(CAM_OPEN_STAGE)) {
			// only the free stage can move to the open stage since all other stages are more advanced than open
			if (currentStage.equals(CAM_OPEN_STAGE) || currentStage.equals(CAM_TAKEPICTURE_STAGE) || currentStage.equals(CAM_STARTPREVIEW_STAGE) || currentStage.equals(CAM_LOCK_STAGE))
				return false;
			else
				return true;
		}	
		else if (nextStage.equals(CAM_LOCK_STAGE)) {
			// Any stages that are more advanced cannot move to the lock stage. Generally, locking is called early
			// on to gain exclusive control over the camera
			if (currentStage.equals(CAM_LOCK_STAGE) || currentStage.equals(CAM_TAKEPICTURE_STAGE) || currentStage.equals(CAM_STARTPREVIEW_STAGE))
				return false;
			else {
				return true;
			}
		}
		else if (nextStage.equals(CAM_STARTPREVIEW_STAGE)) {
			// the startPreview stage is moved to form earlier stages and can be moved to from takePicture, so any stage
			// other than itself is acceptable
			if (currentStage.equals(CAM_STARTPREVIEW_STAGE))
				return false;
			else 
				return true;
		}
		else if (nextStage.equals(CAM_TAKEPICTURE_STAGE)) {
			// the takePicture stage is right before releasing the camera so progress here can happen from any stage
			// in addition after taking a picture, it moves back to the startPreview stage. In addition, people can
			// take multiple pictures
			return true;
		}		
		return false;
	}
	
	
	// standard method called when a method or constructor is hooked by Xposed	
	@Override
	public void handleLoadPackage(LoadPackageParam lpparam) throws Throwable {
		final String callingPackage = lpparam.packageName;
		final long currentNano = System.nanoTime();
		
		if (EXCLUDE_MOST_SYSTEM_APPS) {
    		if (DoSDefenseModule.isExcluded != null) { // check if a check has already been done for this particular apk
    			if (DoSDefenseModule.isExcluded == true) // has already been checked 
    				return; // it has been determined that this app has been excluded
    		}
    		else { 
    			// the first time this app is being checked    			
    			if (DoSDefenseModule.exclusionList.size() == 0) {
    				if (DEBUG)
    					Log.d(TAG, "[" + callingPackage + "] is attempting to get system packages");
    				this.getSystemApps();
    			}
    			
        		if (DoSDefenseModule.exclusionList.contains(callingPackage)) { // check to see if the hooked apk is in the exclusion list
        			// the app is excluded
        			DoSDefenseModule.isExcluded = Boolean.TRUE; // indicate that it is excluded
            		if (DEBUG)
            			Log.d(TAG, callingPackage + " is excluded");
        			return;
        		}
            	else { 
            		// the app is not excluded
            		DoSDefenseModule.isExcluded = Boolean.FALSE;
            		if (DEBUG)
            			Log.d(TAG, callingPackage + " is not excluded");
            	}    			
    		}
		}
		
		findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "open", "int", new XC_MethodHook() {
			@Override
			protected void afterHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.open(int) - " + callingPackage + " - " + currentNano);				
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_OPEN_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_OPEN_STAGE);					
					currentCameraStage = CAM_OPEN_STAGE; 
					cameraOpenTS = new GregorianCalendar();
					cam = (Camera) param.thisObject;
					if (DoSDefenseModule.camWatchdog == null) {
						if (DEBUG)
							Log.d(TAG, "CameraWatchdog thread does not exist. create it");						
						DoSDefenseModule.camWatchdog = new CameraWatchdog();
						Thread thread = new Thread(DoSDefenseModule.camWatchdog);
						thread.start();
					}					
				}
				else
					if (DEBUG)
						Log.d(TAG, "not forward progress: " + currentCameraStage + " -> " + CAM_OPEN_STAGE);
			}
		});
		
		findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "open", new XC_MethodHook() {
			@Override
			protected void afterHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.open() - " + callingPackage + " - " + currentNano);	
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_OPEN_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_OPEN_STAGE);					
					cameraOpenTS = new GregorianCalendar();
					currentCameraStage = CAM_OPEN_STAGE; 					
					cam = (Camera) param.thisObject;
					if (DoSDefenseModule.camWatchdog == null) {
						if (DEBUG)
							Log.d(TAG, "CameraWatchdog thread does not exist. create it");
						DoSDefenseModule.camWatchdog = new CameraWatchdog();
						Thread thread = new Thread(DoSDefenseModule.camWatchdog);
						thread.start();
					}					
				}
				else
					if (DEBUG)
						Log.d(TAG, "not forward progress: " + currentCameraStage + " -> " + CAM_OPEN_STAGE);
			}
		});
		
		
		findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "lock", new XC_MethodHook() {
			@Override
			protected void afterHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.lock() - " + callingPackage + " - " + currentNano);				
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_LOCK_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_LOCK_STAGE);					
					cameraLockTS = new GregorianCalendar();
					currentCameraStage = CAM_LOCK_STAGE; 					
					cam = (Camera) param.thisObject;
					if (DoSDefenseModule.camWatchdog == null) {
						if (DEBUG)
							Log.d(TAG, "CameraWatchdog thread does not exist. create it");
						DoSDefenseModule.camWatchdog = new CameraWatchdog();
						Thread thread = new Thread(DoSDefenseModule.camWatchdog);
						thread.start();
					}					
				}
				else
					if (DEBUG)
						Log.d(TAG, "not forward progress: " + currentCameraStage + " -> " + CAM_LOCK_STAGE);	
			}
		});
		
		findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "startPreview", new XC_MethodHook() {
			@Override
			protected void afterHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.startPreview() - " + callingPackage + " - " + currentNano);
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_STARTPREVIEW_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_STARTPREVIEW_STAGE);										
					cameraOpenPreviewTS = new GregorianCalendar();
					currentCameraStage = CAM_STARTPREVIEW_STAGE;
					cam = (Camera) param.thisObject;
					if (DoSDefenseModule.camWatchdog == null) {
						if (DEBUG)
							Log.d(TAG, "CameraWatchdog thread does not exist. create it");
						DoSDefenseModule.camWatchdog = new CameraWatchdog();
						Thread thread = new Thread(DoSDefenseModule.camWatchdog);
						thread.start();
					}					
				}
				else
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_STARTPREVIEW_STAGE);
			}
		});
		
    	findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "takePicture", "android.hardware.Camera$ShutterCallback", "android.hardware.Camera$PictureCallback", "android.hardware.Camera$PictureCallback", new XC_MethodHook() {
    		@Override
    		protected void afterHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.takePicture(...) - " + callingPackage + " - " + currentNano);
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_TAKEPICTURE_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_TAKEPICTURE_STAGE);					
					cameraTakePictureTS = new GregorianCalendar();    			
	    			currentCameraStage = CAM_TAKEPICTURE_STAGE;					
				}
				else
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_TAKEPICTURE_STAGE);
    		}
    	});

    	findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "takePicture", "android.hardware.Camera$ShutterCallback", "android.hardware.Camera$PictureCallback", "android.hardware.Camera$PictureCallback", "android.hardware.Camera$PictureCallback", new XC_MethodHook() {
    		@Override
    		protected void afterHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.takePicture(...) - " + callingPackage + " - " + currentNano);    			
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_TAKEPICTURE_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_TAKEPICTURE_STAGE);
					cameraTakePictureTS = new GregorianCalendar();    			
	    			currentCameraStage = CAM_TAKEPICTURE_STAGE;					
				}
    		}
    	});		
		
		findAndHookMethod("android.hardware.Camera", lpparam.classLoader, "release", new XC_MethodHook() {
			@Override
			protected void afterHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.hardware.Camera.release() - " + callingPackage + " - " + currentNano);
				
				if (DoSDefenseModule.isForwardProgress(currentCameraStage, CAM_FREE_STAGE)) {
					if (DEBUG)
						Log.d(TAG, "forward progress: " + currentCameraStage + " -> " + CAM_FREE_STAGE);					
					cameraLockTS = null;
					cameraOpenPreviewTS = null;
					cameraTakePictureTS = null;				
					cameraOpenTS = null;
					if (DoSDefenseModule.camWatchdog != null) {
						DoSDefenseModule.camWatchdog.instructStop();
						DoSDefenseModule.camWatchdog = null;
					}
					currentCameraStage = CAM_FREE_STAGE;
					cam = null;					
				}
			}
		});
		
		findAndHookMethod("android.media.MediaRecorder", lpparam.classLoader, "start", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.media.MediaRecorder.start() - " + callingPackage + " - " + currentNano);
				MediaRecorder mr = (MediaRecorder) param.thisObject;
				String path = (String) DoSDefenseModule.this.tryToGetObjectFieldUsingReflection("mPath", mr);
				if (path == null) {
					if (DEBUG)
						Log.d(TAG, "the mPath variable of MediaRecorder is null");
					return;
				}				
				else {
					if (DEBUG)
						Log.d(TAG, "the mPath variable of MediaRecorder is " + path);
					if (path.equals("/dev/null")) {
						throw new IllegalStateException("You cannot record to /dev/null!");
					}
				}									
			}
		});
		
		findAndHookMethod("android.app.ActivityManagerProxy", lpparam.classLoader, "startActivity", "android.app.IApplicationThread", "java.lang.String", "android.content.Intent", "java.lang.String", "android.os.IBinder", "java.lang.String", "int", "int", "java.lang.String", "android.os.ParcelFileDescriptor", "android.os.Bundle", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.app.ActivityManagerNative.startActivity(...) - " + callingPackage + " - " + currentNano);					
				int weight = 1;
				boolean intentNewTask = DoSDefenseModule.willIntentCreateNewTask(param.args[2]);
				if (intentNewTask)
					weight = DoSDefenseModule.NEW_TASK_INTENT_WEIGHT;
				boolean toofast = isRateTooFast(callingPackage, weight);
				if (toofast) {
					if (DEBUG)
						Log.d(TAG, "too fast - return value is " + DoSDefenseModule.INTENT_VALUE_RETURN + " and size of intents is " + weight);
					param.setResult(Integer.valueOf(DoSDefenseModule.INTENT_VALUE_RETURN));						
					return;						
				}
			}
		});
		
		findAndHookMethod("android.app.ActivityManagerProxy", lpparam.classLoader, "startActivityAsUser", "android.app.IApplicationThread", "java.lang.String", "android.content.Intent", "java.lang.String", "android.os.IBinder", "java.lang.String", "int", "int", "java.lang.String", "android.os.ParcelFileDescriptor", "android.os.Bundle", "int", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.app.ActivityManagerNative.startActivityAsUser(...) - " + callingPackage + " - " + currentNano);
				int weight = 1;
				boolean intentNewTask = DoSDefenseModule.willIntentCreateNewTask(param.args[2]);
				if (intentNewTask)
					weight = DoSDefenseModule.NEW_TASK_INTENT_WEIGHT;
				boolean toofast = isRateTooFast(callingPackage, weight);
				if (toofast) {
					if (DEBUG)
						Log.d(TAG, "too fast - return value is " + DoSDefenseModule.INTENT_VALUE_RETURN + " and size of intents is " + weight);
					param.setResult(Integer.valueOf(DoSDefenseModule.INTENT_VALUE_RETURN));						
					return;						
				}
			}
		});

		findAndHookMethod("android.app.ActivityManagerProxy", lpparam.classLoader, "startActivityAndWait", "android.app.IApplicationThread", "java.lang.String", "android.content.Intent", "java.lang.String", "android.os.IBinder", "java.lang.String", "int", "int", "java.lang.String", "android.os.ParcelFileDescriptor", "android.os.Bundle", "int", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.app.ActivityManagerNative.startActivityAndWait(...) - " + callingPackage + " - " + currentNano);
				int weight = 1;
				boolean intentNewTask = DoSDefenseModule.willIntentCreateNewTask(param.args[2]);
				if (intentNewTask)
					weight = DoSDefenseModule.NEW_TASK_INTENT_WEIGHT;
				boolean toofast = isRateTooFast(callingPackage, weight);
				if (toofast) {
					if (DEBUG)
						Log.d(TAG, "too fast - return value is " + DoSDefenseModule.INTENT_VALUE_RETURN + " and size of intents is " + weight);
					param.setResult(Integer.valueOf(DoSDefenseModule.INTENT_VALUE_RETURN));						
					return;						
				}
			}
		});

		findAndHookMethod("android.app.ActivityManagerProxy", lpparam.classLoader, "startActivityWithConfig", "android.app.IApplicationThread", "java.lang.String", "android.content.Intent", "java.lang.String", "android.os.IBinder", "java.lang.String", "int", "int", "android.content.res.Configuration", "android.os.Bundle", "int",  new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.app.ActivityManagerNative.startActivityWithConfig(...) - " + callingPackage + " - " + currentNano);
				int weight = 1;
				boolean intentNewTask = DoSDefenseModule.willIntentCreateNewTask(param.args[2]);
				if (intentNewTask)
					weight = DoSDefenseModule.NEW_TASK_INTENT_WEIGHT;
				boolean toofast = isRateTooFast(callingPackage, weight);
				if (toofast) {
					if (DEBUG)
						Log.d(TAG, "too fast - return value is " + DoSDefenseModule.INTENT_VALUE_RETURN + " and size of intents is " + weight);
					param.setResult(Integer.valueOf(DoSDefenseModule.INTENT_VALUE_RETURN));						
					return;						
				}
			}
		});
		
		findAndHookMethod("android.app.ActivityManagerProxy", lpparam.classLoader, "startActivityIntentSender", "android.app.IApplicationThread", "android.content.IntentSender", "android.content.Intent", "java.lang.String", "android.os.IBinder", "java.lang.String", "int", "int", "int", "android.os.Bundle", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.app.ActivityManagerNative.startVoiceActivity(...) - " + callingPackage + " - " + currentNano);
				int weight = 1;
				boolean intentNewTask = DoSDefenseModule.willIntentCreateNewTask(param.args[2]);
				if (intentNewTask)
					weight = DoSDefenseModule.NEW_TASK_INTENT_WEIGHT;
				boolean toofast = isRateTooFast(callingPackage, weight);
				if (toofast) {
					if (DEBUG)
						Log.d(TAG, "too fast - return value is " + DoSDefenseModule.INTENT_VALUE_RETURN + " and size of intents is " + weight);
					param.setResult(Integer.valueOf(DoSDefenseModule.INTENT_VALUE_RETURN));						
					return;						
				}
			}
		});
				
		findAndHookMethod("android.app.ActivityManagerProxy", lpparam.classLoader, "startActivities", "android.app.IApplicationThread", "java.lang.String", "android.content.Intent[]", "java.lang.String[]", "android.os.IBinder", "android.os.Bundle", "int", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {		
				if (DEBUG)
					Log.d(TAG, "android.app.ActivityManagerNative.startActivities(...) - " + callingPackage + " - " + currentNano);
				Object[] params = param.args;
				if (params != null) {
					
					Intent[] intents = (Intent[]) params[2];
					String[] strArr = (String[]) params[3];
					
					if (intents == null || strArr == null)
						return;
					
					// if more are being sent then truncate it to the maximum number of intents that can 
					// be sent for the short counter
					int weightedCounter = 0;
					int newNumIntents = 0;
					int index = 0;
					boolean keepGoing = true;
					while (keepGoing) {
						Intent anIntent = intents[index++];
						if (DoSDefenseModule.willIntentCreateNewTask(anIntent)) {
							if ((weightedCounter + NEW_TASK_INTENT_WEIGHT) <= INTENT_MAX_COUNT_SHORT) {
								weightedCounter+= NEW_TASK_INTENT_WEIGHT;
								newNumIntents++;
							}
							else
								keepGoing = false;									
						}
						else {
							if ((weightedCounter + 1) <= INTENT_MAX_COUNT_SHORT) {
								weightedCounter++;
								newNumIntents++;
							}
							else
								keepGoing = false;
						}
						if (weightedCounter == INTENT_MAX_COUNT_SHORT) {
							keepGoing = false;										
						}
					}

					if (DEBUG)
						Log.d(TAG, "Original count was " + intents.length + " and new weighted count is " + newNumIntents);

					Intent[] newIntents = new Intent[newNumIntents];						
					for (int a = 0; a < newNumIntents; a++) {
						newIntents[a] = intents[a];
					}						
					params[2] = newIntents;						

					String[] something = new String[newNumIntents];
					for (int a = 0; a < newNumIntents; a++) {
						something[a] = strArr[a];
					}						
					params[3] = something;						

					boolean toofast = isRateTooFast(callingPackage, newIntents.length);					
					if (toofast) {		
						if (DEBUG)
							Log.d(TAG, "too fast - return value is " + DoSDefenseModule.INTENT_VALUE_RETURN + " and size of intents is " + newIntents.length);
						param.setResult(Integer.valueOf(DoSDefenseModule.INTENT_VALUE_RETURN));
						return;						
					}
				}					
			}
		});
		
		findAndHookMethod("android.app.PendingIntent", lpparam.classLoader, "send", "android.content.Context", "int", "android.content.Intent", "android.app.PendingIntent$OnFinished", "android.os.Handler", new XC_MethodHook() {
			@Override
			protected void beforeHookedMethod(MethodHookParam param) throws Throwable {
				if (DEBUG)
					Log.d(TAG, "android.app.PendingIntent.send(android.content.Context,int,android.content.Intent,android.app.PendingIntent$OnFinished,android.os.Handler) - " + callingPackage + " - " + currentNano);
								
				Object[] params = param.args;
				boolean willStartNewTask = false;
				int weight = 1;
				PendingIntent pi = (PendingIntent) param.thisObject;
				
				try {
					DoSDefenseModule.appContext = (Context) params[0];	
				}
				catch (ClassCastException e) {
					DoSDefenseModule.appContext = null;
				}								
				
				if (pi != null) {
					String packCreator = pi.getCreatorPackage();
					if (DEBUG)
						Log.d(TAG, "the creator package is " + packCreator);
					
					try {
						Class piClass = pi.getClass();					
						Method method = piClass.getDeclaredMethod("getIntent", new Class[0]);
						method.setAccessible(true);
						Object ret = method.invoke(pi, new Object[0]);
						Intent i = (Intent) ret;
						if (DoSDefenseModule.willIntentCreateNewTask(i)) {
							willStartNewTask = true;
						}							
					} catch (Exception e) {}
				}

				if (willStartNewTask) {
					weight = DoSDefenseModule.NEW_TASK_INTENT_WEIGHT;
				}				
				boolean toofast = isRateTooFast(callingPackage, weight);				
				if (toofast) {					
					if (DEBUG)
						Log.d(TAG, "too fast - return value is null and size of intents is " + weight);
					
					if (DoSDefenseModule.REMOVE_PENDING_INTENTS_FROM_ALARM_MANAGER && appContext != null) {
						AlarmManager am = (AlarmManager) appContext.getSystemService(Context.ALARM_SERVICE);
						String piStr = param.thisObject.toString();
						am.cancel((PendingIntent) param.thisObject); 
						if (DEBUG)
							Log.d(TAG, "Canceled PendingIntent - " + piStr);
					}					
					param.setResult(null);
					return;						
				}
			}
		});
		
		
	}
	
	// a thread to examine an app's progression through the stages of using the camera
	static class CameraWatchdog implements Runnable {
		
		private boolean keepGoing = true; // if true, the thread will continue execution
		private final static String TAG = CameraWatchdog.class.getName(); // Tag for writing to the Android log
		
		CameraWatchdog() {}
		
		// called when the thread is to stop running
		void instructStop() {			
			keepGoing = false;
		}
		
		@Override
		public void run() {

			if (DEBUG)
				Log.d(TAG, "CameraWatchdog thread started");
			
			while (keepGoing) {
				
				// sleep a little to prevent busy waiting
				try {
					Thread.sleep(1000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				
				GregorianCalendar currentTS = new GregorianCalendar(); // create a calendar
				Date d2 = currentTS.getTime(); // obtain the current time data			 
				long mil2 = d2.getTime(); // obtain the current time
								
				if (DoSDefenseModule.currentCameraStage.equals(CAM_FREE_STAGE)) {
					// if the camera is free, then this thread is no longer needed
					keepGoing = false;
				}
				else if (DoSDefenseModule.currentCameraStage.equals(CAM_OPEN_STAGE)) {
					// calculate the time difference in seconds from when the startPreview method was called and now
					Date d1 = cameraOpenTS.getTime(); 				
					long mil1 = d1.getTime(); 
					long diff9 = mil2 - mil1; 
					int diff2 = (int) diff9; 
					int an = diff2 / 1000; 					
					if (DEBUG)
						Log.d(TAG, DoSDefenseModule.currentCameraStage + " - time delta is " + an + " seconds");					
					if (an >= DoSDefenseModule.MOVE_FROM_OPEN) {								
						if (DoSDefenseModule.cam != null) {
							DoSDefenseModule.cam.unlock();
							DoSDefenseModule.cam.release();							
							if (DoSDefenseModule.KILL_APP_THAT_DOES_NOT_PROGRESS_ON_CAMERA)
								android.os.Process.killProcess(android.os.Process.myPid());
						}							
						if (DEBUG)
							Log.d(TAG, "time exceeded by spending too much time by holding camera and not progressing!");
						// the camera has been stripped from the app, so the thread is no longer needed
						keepGoing = false;
					}	

				}
				else if (DoSDefenseModule.currentCameraStage.equals(CAM_LOCK_STAGE)) {
					// calculate the time difference in seconds from when the startPreview method was called and now
					Date d1 = cameraLockTS.getTime(); 				
					long mil1 = d1.getTime(); 
					long diff9 = mil2 - mil1; 
					int diff2 = (int) diff9; 
					int an = diff2 / 1000; 					
					if (DEBUG)
						Log.d(TAG, DoSDefenseModule.currentCameraStage + " - time delta is " + an + " seconds");					
					if (an >= DoSDefenseModule.MOVE_FROM_LOCK) {								
						if (DoSDefenseModule.cam != null) {
							DoSDefenseModule.cam.unlock();
							DoSDefenseModule.cam.release();							
							if (DoSDefenseModule.KILL_APP_THAT_DOES_NOT_PROGRESS_ON_CAMERA)
								android.os.Process.killProcess(android.os.Process.myPid());
						}
						if (DEBUG)
							Log.d(TAG, "time exceeded by spending too much time by holding camera and not progressing!");
						// the camera has been stripped from the app, so the thread is no longer needed
						keepGoing = false;
					}					
					
				}				
				else if (DoSDefenseModule.currentCameraStage.equals(CAM_STARTPREVIEW_STAGE)) {					
					// calculate the time difference in seconds from when the startPreview method was called and now
					Date d1 = cameraOpenPreviewTS.getTime(); 				
					long mil1 = d1.getTime(); 
					long diff9 = mil2 - mil1; 
					int diff2 = (int) diff9; 
					int an = diff2 / 1000; 					
					if (DEBUG)
						Log.d(TAG, DoSDefenseModule.currentCameraStage + " - time delta is " + an + " seconds");					
					if (an >= DoSDefenseModule.MOVE_FROM_STARTPREVIEW) {								
						if (DoSDefenseModule.cam != null) {
							DoSDefenseModule.cam.unlock();
							DoSDefenseModule.cam.release();							
							if (DoSDefenseModule.KILL_APP_THAT_DOES_NOT_PROGRESS_ON_CAMERA)
								android.os.Process.killProcess(android.os.Process.myPid());
						}							
						if (DEBUG)
							Log.d(TAG, "time exceeded by spending too much time by holding camera and not progressing!");
						// the camera has been stripped from the app, so the thread is no longer needed
						keepGoing = false;
					}	
					
				}
				else if (DoSDefenseModule.currentCameraStage.equals(CAM_TAKEPICTURE_STAGE)) {
					// calculate the time difference in seconds from when the takePicture method was called and now
					Date d1 = cameraTakePictureTS.getTime(); 				
					long mil1 = d1.getTime(); 
					long diff9 = mil2 - mil1; 
					int diff2 = (int) diff9; 
					int an = diff2 / 1000; 					
					if (DEBUG)
						Log.d(TAG, DoSDefenseModule.currentCameraStage + " - time delta is " + an + " seconds");					
					if (an >= DoSDefenseModule.MOVE_FROM_TAKEPICTURE) {								
						if (DoSDefenseModule.cam != null) {
							DoSDefenseModule.cam.unlock();
							DoSDefenseModule.cam.release();
							if (DoSDefenseModule.KILL_APP_THAT_DOES_NOT_PROGRESS_ON_CAMERA)
								android.os.Process.killProcess(android.os.Process.myPid());
						}						
						if (DEBUG)
							Log.d(TAG, "time exceeded by spending too much time by holding camera and not progressing!");
						// the camera has been stripped from the app, so the thread is no longer needed
						keepGoing = false;
					}	
				}			
			}	
			if (DEBUG)
				Log.d(TAG, "CameraWatchdog thread ended");
		}
	}
}
