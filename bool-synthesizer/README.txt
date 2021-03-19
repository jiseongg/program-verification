
1. The format of specification

```
N			(the number of boolean variables)
p			(the number of positive examples)
n 		(the number of negative examples)
--positive--
0....1
...
--negative--
0....1
...
```

2. How to use

python3 synth_bool.py <specification_file>

3. result

Result example for nor
```
f(X) = (!x1 /\ !x2)
```

If no solution exist,
```
no solution exist
```
