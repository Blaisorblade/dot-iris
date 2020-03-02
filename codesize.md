# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
094a2355b70144e6c198a504f823fe4c4db957ab.

```
theories: 1021
theories/iris_extra: 1324
theories/Dot: 212
theories/Dot/stamping: 2562
theories/Dot/misc_unused: 1434
theories/Dot/typing: 2820
theories/Dot/syn: 2095
theories/Dot/examples: 4199
theories/Dot/lr: 2613
theories/misc_unused: 616
theories/DSub/stamping: 1016
theories/DSub/misc_unused: 75
theories/DSub/typing: 226
theories/DSub/syn: 654
theories/DSub/lr: 227
theories/DSubSyn: 153
theories/DSubSyn/typing: 226
theories/DSubSyn/lr: 530
theories/pure_program_logic: 730

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 2125

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 17576

Preliminaries (. iris_extra pure_program_logic): 3075

DOT (Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 14501

syntax (syn): 2095
logrel (lr): 2613
model (syntax + logrel) (syn lr): 4708

syntactic typing (w/ stamping) (. typing stamping): 5594

examples (examples): 4199
```
