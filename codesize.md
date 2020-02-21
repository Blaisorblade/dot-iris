# Code size statistics

They were computed by running `./codesize.sh` on commit 
7a9b4e14caa907b1d7cde7520f46c97a62877cfc.

Saved output:
```
$ ./codesize.sh
theories: 1021
theories/iris_extra: 1324
theories/Dot: 194
theories/Dot/stamping: 2648
theories/Dot/misc_unused: 1327
theories/Dot/typing: 2645
theories/Dot/syn: 1845
theories/Dot/examples: 4239
theories/Dot/lr: 2613
theories/misc_unused: 616
theories/DSub/stamping: 1016
theories/DSub/misc_unused: 75
theories/DSub/typing: 226
theories/DSub/syn: 656
theories/DSub/lr: 227
theories/DSubSyn: 153
theories/DSubSyn/typing: 226
theories/DSubSyn/lr: 530
theories/pure_program_logic: 730

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 2018

Preliminaries + DOT (. iris_extra pure_program_logic Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 17259

Preliminaries (. iris_extra pure_program_logic): 3075

DOT (Dot Dot/stamping Dot/typing Dot/syn Dot/examples Dot/lr): 14184

syntax (syn): 1845
logrel (lr): 2613
model (syntax + logrel) (syn lr): 4458

syntactic typing (w/ stamping) (. typing stamping): 5487

examples (examples): 4239
```
