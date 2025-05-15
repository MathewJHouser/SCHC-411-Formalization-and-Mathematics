def test : String := 
"4035
10596
17891
5278

11293
8478
10874
10582
10756
6649

9707
15243
13494

18006
15104
9091

1177
5310
4579
2550
3865
4871
3455
3129
2853
2521
3656
4203
5381
1300
1054

6249
6107
4509
6066
6204
4054
1040
4447
1325
5283
4176
2281
1895"

#eval test

def elves (s : String) : List String := s.splitOn "\x0d\n\x0d\n"

#eval elves test 

def calories (s: String) : List Nat := 
  let l' := s.splitOn "\x0d\n"
  l'.map (fun s => s.toNat!)

#eval (elves test).map calories

def addUp (l: List Nat) : Nat :=
l.foldl (· + · ) 0

#eval addUp [1,2,3,4,5]

#eval (elves test).map calories

def totalCalList (s: String): List Nat :=
let t := elves s
let l' := t.map calories 
l'.map addUp 

#eval totalCalList test 

def answer (s: String) : Nat := 
  totalCalList s|>.foldl max 0 

#eval answer test


