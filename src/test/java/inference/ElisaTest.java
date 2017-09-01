package inference;

import org.apache.commons.cli.CommandLine;
import org.apache.logging.log4j.core.config.plugins.PluginBuilderFactory;
import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import config.Config;

/**
 * @created: 9/1/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public class ElisaTest {

    public static String root = "tests/elisa/";

    @Test
    public void broadSpectrumOpiateSat() {
        String file = "broad_spectrum_opiate.json";
        CommandLine.Builder cmd = new CommandLine.Builder();
    }

    @Test
    public void ciprofloxacinSat() {
        String file = "ciprofloxacin.json";
    }

    @Test
    public void diazepamSat() {
        String file = "diazepam.json";
    }

    @Test
    public void dilutionSat() {
        String file = "dilution.json";
    }

    @Test
    public void fentanylSat() {
        String file = "fentanyl.json";
    }

    @Test
    public void fullMorphineSat() {
        String file = "full_morphone.json";
    }

    @Test
    public void heroineSat() {
        String file = "heroine.json";
    }

    @Test
    public void morphineSat() {
        String file = "morphine.json";
    }

    @Test
    public void oxycodoneSat() {
        String file = "oxycodone.json";
    }
}
