# Code size statistics

Computed by running `./codesize.sh > codesize.md` on commit
646d4f6c7ec5f4913519ffcc3cd6052cab8dc23c.

```
theories: 1022
theories/iris_extra: 1327
theories/Dot: 212
theories/Dot/stamping: 2562
theories/Dot/misc_unused: 1434
theories/Dot/typing: 2820
theories/Dot/syn: 2095
theories/Dot/examples: 4193
theories/Dot/lr: 2604
theories/misc_unused: 616
theories/DSub/stamping: 1016
theories/DSub/misc_unused: 75
theories/DSub/typing: 226
theories/DSub/syn: 654
theories/DSub/lr: 219
theories/DSubSyn: 152
theories/DSubSyn/typing: 226
theories/DSubSyn/lr: 521
theories/pure_program_logic: 730

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 2125

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 17565

Preliminaries (. iris_extra pure_program_logic): 3079

DOT (Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 14486

syntax (syn): 2095
logrel (lr): 2604
model (syntax + logrel) (syn lr): 4699

syntactic typing (w/ stamping) (. typing stamping): 5594

examples (examples): 4193
```
