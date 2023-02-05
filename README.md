
# Proof Builder


A curses-based natural deduction proof editor.
  
usage:

-f: required argument to specify the formula to be proven as valid

connectives in the formulas should be replaced with the following characters:  

f:\forall e:\exists t:\top i:\supset q:\equiv o:\lor b:\bot

_the window size should be at least 180 x 35_

sample usage:  

```python3 proof_builder.py -f 'ex(P(x) o -P(x))'```
