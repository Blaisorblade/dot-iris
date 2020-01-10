# Code size statistics

They were computed by running `./codesize.sh` on commit 
dc77af3fe941b04cd7a98480ca1329c79a40c04f.

Saved output:
```
$ ./codesize.sh
theories: 943
theories/iris_extra: 1088
theories/Dot: 143
theories/Dot/stamping: 2505
theories/Dot/misc_unused: 1300
theories/Dot/typing: 2045
theories/Dot/syn: 1304
theories/Dot/examples: 2650
theories/Dot/lr: 1898
theories/misc_unused: 1275
theories/DSub/stamping: 1010
theories/DSub/misc_unused: 72
theories/DSub/typing: 226
theories/DSub/syn: 650
theories/DSub/lr: 287
theories/DSubSyn: 150
theories/DSubSyn/typing: 226
theories/DSubSyn/lr: 523
theories/pure_program_logic: 730

Unused (misc_unused Dot/misc_unused DSub/misc_unused): 2647

Preliminaries (. iris_extra pure_program_logic): 2761

DOT (. ./stamping ./typing ./syn ./examples ./lr): 10545

syntax (syn): 1304
logrel (lr): 1898
model (syntax + logrel) (syn lr): 3202

syntactic typing (w/ stamping) (. typing stamping): 4693

examples (examples): 2650
```
