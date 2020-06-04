# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
b0f1ebc209fc41a62b8c97607c267bc2e87a5b71.

```
theories: 1033
theories/iris_extra: 1591
theories/Dot: 158
theories/Dot/hkdot: 1627
theories/Dot/semtyp_lemmas: 1544
theories/Dot/typing: 680
theories/Dot/syn: 3134
theories/Dot/examples: 688
theories/Dot/examples/old_typing: 1538
theories/Dot/examples/sem: 2200
theories/Dot/examples/sem/semtyp_lemmas: 427
theories/Dot/examples/stamping: 773
theories/Dot/examples/syn: 1202
theories/Dot/lr: 2133
theories/DSub: 153
theories/DSub/typing: 229
theories/DSub/syn: 637
theories/DSub/lr: 590
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/hkdot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn Dot/lr): 19048

Preliminaries (. iris_extra pure_program_logic): 2944

DOT (Dot Dot/hkdot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn Dot/lr): 16104

syntax (syn): 3134
logrel (lr semtyp_lemmas): 3677
model (syntax + logrel) (syn lr semtyp_lemmas): 6811

syntactic typing (w/ fundamental) (. typing): 838

examples (examples examples/old_typing examples/sem examples/sem/semtyp_lemmas examples/stamping examples/syn): 6828

hkdot (hkdot): 1627
```
