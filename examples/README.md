## Search

The example about State Space Search is at [map/map.c][]:
There are two update points inserted in the function "ShortestPath", and this function 
is called twice, and other two points are inserted in the "main". There are six times 
that "updatepoint" is executed. The result of "UPSEARCH=1 ./map" shows fives possible path as below:

$ kcc -d-s map.c patch.c -o map
$ UPSEARCH=1 ./map  
Searching reachable states... (with non-deterministic update)
========================================================================
5 solutions found
------------------------------------------------------------------------
Solution 1
Program completed successfully
Exit code: 0
Update at Line:77
Output:
ListItem(# ""(.KList))
ListItem(# "welcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)DDD(4)eee\n\nwelcome to travel map !\n\nfrom aaa to bbb the best path is (the shortest distance is 2098km.)\n\taaa --> ccc  --> bbb \n\n\n999\n"(.KList))
ListItem(# ""(.KList))
------------------------------------------------------------------------
Solution 2
Program completed successfully
Exit code: 0
Update at Line:156
Output:
ListItem(# ""(.KList))
ListItem(# "welcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)DDD(4)eee\n\nwelcome to travel map !\n\nfrom aaa to bbb the best path is (the shortest distance is 2098km.)\n\taaa --> ccc  --> bbb \n\n\n999\n"(.KList))
ListItem(# ""(.KList))
------------------------------------------------------------------------
Solution 3
Program completed successfully
Exit code: 0
Update at Line:77
Output:
ListItem(# ""(.KList))
ListItem(# "welcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\nwelcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\n10\n"(.KList))
ListItem(# ""(.KList))
------------------------------------------------------------------------
Solution 4
Program completed successfully
Exit code: 0
Update at Line:
Output:
ListItem(# ""(.KList))
ListItem(# "welcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\nwelcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\n10\n"(.KList))
ListItem(# ""(.KList))
------------------------------------------------------------------------
Solution 5
Program completed successfully
Exit code: 0
Update at Line:162
Output:
ListItem(# ""(.KList))
ListItem(# "welcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\nwelcome to travel map !\n\nthe city list is shown below:\n\n(0)aaa(1)bbb(2)ccc(3)ddd(4)eee\n\nfrom aaa to bbb the best path is (the shortest distance is 2108km.)\n\taaa --> ccc  --> bbb \n\n\n10\n"(.KList))
ListItem(# ""(.KList))
========================================================================
5 solutions found

The first update point in "ShortestPath" violates the version consistency, because the body should be considered as a transaction during one computation. 
And the second point in "ShortestPath" responds to the solution 1 and solution 3 as above. 
The update poins in "main" respond to the solution 2 and solution 5.
The solution 4 is the situation that the update does not  happen showing "Update at Line" is empty.

The updated functions do not make effect until the next call. 


## LTL model checking

NOTE: LTL model checking seems to be broken in recent versions of K.


### Syntax

The syntax of LTL formulas is given by the following grammar:
```
LTL ::= "~Ltl" LTL
      | "OLtl" LTL
      | "<>Ltl" LTL
      | "[]Ltl" LTL
      | LTL "/\Ltl" LTL
      | LTL "\/Ltl" LTL
      | LTL "ULtl" LTL
      | LTL "RLtl" LTL
      | LTL "WLtl" LTL
      | LTL "|->Ltl" LTL
      | LTL "->Ltl" LTL 
      | LTL "<->Ltl" LTL
      | LTL "=>Ltl" LTL 
      | LTL "<=>Ltl" LTL
```

Besides, this basic formulas, we also add the logical expression, i.e. "==", "!=".
Additionally, We support other special atomic propositions: `__update`.
It is false when the updating dose not happen and becomes true when the updating occurs. 

### Examples

For example, consider the C program at [light/light.c][]:


The resource of the non-determinism is the order of the addition and the occurrence of the updating.

Using LTL model checking, we can verify that our algorithm is "safe" in the
sense that at least one light is red at all times:
```
$ kcc -s lights.c -o light
$ LTLMC="[]Ltl (lightsNS == 'R' \/Ltl lightsEW == 'R')" ./light
LTL model checking... (with non-deterministic update)
true
```

But we can also discover that we are not guaranteed that a light will eventually
turn green. The following should produce a counter-example:
```
$ LTLMC="[]Ltl <>Ltl lightNS == 'G' " ./light
```
We can fix this by updating the `changeNS()` and `changeEW()` making them contain the global variable `global`.
`global` ensures that the lights  will become green in turns.
after tht udpating, both formulas will hold.


[map/map.c]: map/map.c
[light/lights.c]: light/lights.c
