package utils;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.lang3.StringUtils;

import java.lang.reflect.Method;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class CommonUtils {

    public static CommandLine buildCommandLine(String args) {
        try {
            return new DefaultParser().parse(getOptionsFromMain(), StringUtils.split(args, " "));
        } catch(Exception e) {}
        return null;
    }

    private static Options getOptionsFromMain() {
        try {
            Class<?> c = Class.forName("Main");
            Object t = c.newInstance();

            for (Method m : c.getDeclaredMethods()) {
                // Note the second string *must* match with the declaration in Main.
                if (StringUtils.equalsIgnoreCase(m.getName(), "buildoptions")) {
                    m.setAccessible(true);
                    return (Options) m.invoke(t);
                }
            }
        } catch(Exception e) {

        }
        return new Options();
    }
}
