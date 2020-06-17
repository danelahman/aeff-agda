# Agda formalisation of the AEff language

- The formalisation has been tested with Agda version 2.6.1 and standard library version 1.3.

- The unicode symbols used in the source code have tested to display correctly with the DejaVu Sans Mono font.

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

- `Finality.agda` - proof that the result forms of computations are final, i.e., they do not reduce further

- `ProcessFinality.agda` - proof that the result forms of processes are final, i.e., they do not reduce further
