# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
d4b268a081d4afb02774a620dae43b1d92e723e3.

```
theories: 804
theories/iris_extra: 1538
theories/Dot: 158
theories/Dot/semtyp_lemmas: 1250
theories/Dot/typing: 676
theories/Dot/syn: 2702
theories/Dot/examples: 742
theories/Dot/examples/old_typing: 1316
theories/Dot/examples/sem: 1967
theories/Dot/examples/sem/semtyp_lemmas: 615
theories/Dot/examples/stamping: 168
theories/Dot/examples/syn: 1198
theories/Dot/lr: 1953
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 9401
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 6006
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 15407

Preliminaries (. iris_extra pure_program_logic): 2662

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 6739

syntax (syn): 2702
logrel (lr semtyp_lemmas): 3203
model (syntax + logrel) (syn lr semtyp_lemmas): 5905

syntactic typing (w/ fundamental) (. typing): 834

hkdot (hkdot): 0

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 6006
```
