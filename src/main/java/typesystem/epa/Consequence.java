package typesystem.epa;

/**
 * @created: 9/13/17
 * @since: 0.1
 * @project: ChemicalCompiler
 */
public enum Consequence {
    H {
        @Override
        public String toString() {
            return super.toString() + " Heat Generation";
        }
    },
    F {
        @Override
        public String toString() {
            return super.toString() + " Fire";
        }
    },
    G {
        @Override
        public String toString() {
            return super.toString() + " Innocuous and non-Flammable Gas generation";
        }
    },
    GT {
        @Override
        public String toString() {
            return super.toString() + " Toxic Gas Formation";
        }
    },
    GF {
        @Override
        public String toString() {
            return super.toString() + " Flammable Gas Formation";
        }
    },
    E {
        @Override
        public String toString() {
            return super.toString() + " Explosion";
        }
    },
    P {
        @Override
        public String toString() {
            return super.toString() + " Violent Polymerization";
        }
    },
    S {
        @Override
        public String toString() {
            return super.toString() + " Solubilization of Toxic Substance";
        }
    },
    U {
        @Override
        public String toString() {
            return super.toString() + " Unknown";
        }
    },
    WRS {
        @Override
        public String toString() {
            return " Water Reactive Substance";
        }
    },
    N {
        @Override
        public String toString() {
            return "Incompatible";
        }
    },
    C {
        @Override
        public String toString() {
            return "Caution";
        }
    },
    SR {
        @Override
        public String toString() {
            return "Self Reactive";
        }
    }
}
