See [INSTALL.md](INSTALL.md) for installation instructions.

## Quick Overview
KupC embeds an extension of KCC as a component working with other five additional components. 
We extend KCC by introducing other new preserved words to point out the update point and the transaction range. The keyword indicates a possible place in program where updating can take effect and the lexical scope where maintains the version consistency. The extension of KCC is capable of compiling an updatable C program to the code executable on K Framework.

## Runtime features

Once `kcc` has been run on C source files, it should produce an executable
script (`a.out` by default).

### Searching the state-space of non-deterministic behaviors of update points 

Running `UPSEARCH=1 ./a.out` will exhaustively search the state space resulting
from considering all possible expression sequencings (as allowed by the
standard).
This is the only way to check all possible evaluation orders of a program to
find undefined behavior.

### LTL model checking for updating 

We also support LTL model checking of the possible executions resulting from
considering different expression sequencings.

The examples about the State Space Search and LTL Model Checking can be viewed in [examples].
