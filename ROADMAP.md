# Roadmap

1. Enumerate every dependent Core critical pair, either construct joins or add a
   minimal checked counterexample, then discharge or refute unconditional
   `Core.localConfluent`.
2. Add a fully concrete finite provider/consumer catalog instantiating
   `ObservedReplacementCompatible`, alongside the generic explicit derivation
   already checked in `Cordis.Examples.Replacement`.
3. Add an observational trace model for iterators, async work, failure, realms,
   dynamic child registration, and an explicit refinement relation to an actual
   Cordis implementation.

Additional future work includes HMR transaction semantics and executable model
checking over bounded catalogs.
