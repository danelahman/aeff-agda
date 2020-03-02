# Agda formalisation of the AEff language

- `EffectAnnotations.agda` - effect annotations for signals and interrupt handlers

- `Types.agda` - value, computation, and process types

- `AEff.agda` - well-typed values, computations, and processes (we do not consider untyped terms)

- `Renamings.agda` - renamings for values, computations, and processes

- `Substitutions.agda` - substitutions for values, computations, and processes

- `Preservation.agda` - small-step operational semantics for computations (also serves as a preservation proof)

- `AwaitingComputations.agda` - characterisation of computations that are temporarily blocked awaiting a promise

- `Progress.agda` - proof of progress for the small-step operational semantics of computations

- `ProcessPreservation.agda` - small-step operational semantics for processes (also serves as a preservation proof)

- `ProcessProgress.agda` - proof of progress for the small-step operational semantics of processes
