/**
 * File: src/MciaUtil/HPClassLoader.java
 * -------------------------------------------------------------------------------------------
 * Date			Author      Changes
 * -------------------------------------------------------------------------------------------
 * 07/27/13		hcai		created; for running, multiple times in a single JVM session, 
 *							client class with *Static* field but without "safe" user-defined static 
 *							initializer that is ensured to be called at the beginning of the entry method
 *							@note:	simply using a ClassLoader with SystemClassLoader as parent loader
 *								  would cause abnormal program behaviours with these clients because 
 *								  the static variables would only be initialized ONCE across all the runs
 *								  within the single JVM session!
 *  
*/
package MciaUtil;

import java.io.DataInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;

public class HPClassLoader extends ClassLoader {
	/** client class name that is desired to be loaded in this customized way rather than
	 * by system class loader in default
	 */
	protected String clsname;
	
    public HPClassLoader(String _clsname, String _clsPath) {
        super(getSystemClassLoader()/*HPClassLoader.class.getClassLoader()*/);
        clsname = _clsname;
    }
 
    /**
     * Loads a given class from .class file just like
     * the default ClassLoader. This method could be
     * changed to load the class over network from some
     * other server or from the database.
     *
     * @param name Full class name
     */
    private synchronized  Class<?> getClass(String name)
        throws ClassNotFoundException {
 
    	Class<?> cls = findLoadedClass(name);
        if (cls != null) {
            return cls;
        }
 
        String file = name.replace('.', File.separatorChar)  + ".class";
        byte[] b = null;
        try {
            b = loadClassData(file);
            // defineClass is inherited from the ClassLoader class
            // and converts the byte array into a Class
            cls = defineClass(name, b, 0, b.length);
            resolveClass(cls);
            return cls;
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }
 
    @Override
    public Class<?> loadClass(String name)
        throws ClassNotFoundException {
        //System.out.println("loading class '" + name + "'");
        if (name.contains(clsname)) {
            return getClass(name);
        }
        return super.loadClass(name);
    }
 
    private byte[] loadClassData(String name) throws IOException {
        // Opening the file
        InputStream stream = getClass().getClassLoader().getResourceAsStream(name);
        int size = stream.available();
        byte buff[] = new byte[size];
        DataInputStream in = new DataInputStream(stream);
        // Reading the binary data
        in.readFully(buff);
        in.close();
        return buff;
    }
}

/* vim :set ts=4 tw=4 tws=4 */
