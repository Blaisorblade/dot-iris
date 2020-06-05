# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
59ed9c20b1e0fee8f7e0a70854b9c712c0878340.

```
theories: 1033
theories/iris_extra: 1591
theories/Dot: 158
theories/Dot/hkdot: 1627
theories/Dot/semtyp_lemmas: 1544
theories/Dot/typing: 680
theories/Dot/syn: 3134
theories/Dot/examples: 688
theories/Dot/examples/old_typing: 1539
theories/Dot/examples/sem: 2200
theories/Dot/examples/sem/semtyp_lemmas: 427
theories/Dot/examples/stamping: 773
theories/Dot/examples/syn: 1202
theories/Dot/lr: 2132
theories/DSub: 153
theories/DSub/typing: 229
theories/DSub/syn: 637
theories/DSub/lr: 588
theories/pure_program_logic: 320

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 0

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 10592
Examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 6829
Preliminaries + DOT + examples (. iris_extra pure_program_logic Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 17421

Preliminaries (. iris_extra pure_program_logic): 2944

DOT (Dot Dot/semtyp_lemmas Dot/typing Dot/syn Dot/lr): 7648

syntax (syn): 3134
logrel (lr semtyp_lemmas): 3676
model (syntax + logrel) (syn lr semtyp_lemmas): 6810

syntactic typing (w/ fundamental) (. typing): 838

hkdot (hkdot): 1627

examples (Dot/examples Dot/examples/old_typing Dot/examples/sem Dot/examples/sem/semtyp_lemmas Dot/examples/stamping Dot/examples/syn): 6829
```
