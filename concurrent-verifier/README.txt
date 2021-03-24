

1. The format of specification

```
N			(the maximum step considered)
p			(the number of states of each thread)
n 		(the number of shared variables)
--threadA--
...
...
--threadB--
...
...
```

2. How to use

python3 concurrent-verifier.py <model_file>

3. Result

# violated
```
Safe when r is 1
...
Safe when r is M-1

Mutual exclusion could be violated in M step:
  (0, 0, False, ...)
  ...
```

# verified
```
Safe when r is 1
...
Safe when r is N

Mutual exclusion is proved within N steps
```
