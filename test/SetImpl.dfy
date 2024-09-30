function Exp(n: nat, e: nat): nat {
  if e == 0 then 1
  else n * Exp(n, e - 1)
}

type nat32 = n: int | 0 <= n < Exp(2, 32)

method CreateS1() returns (s1: set<nat32>) 
  {
    s1 := {};
    
    for i := 0 to 1000
    {
      s1 := s1 + {i * 62};
    }
    for i := 0 to 100
    {
      s1 := s1 + {4 * Exp(2, 16) + i};
    }
    for i := 0 to Exp(2, 15)
    {
      s1 := s1 + {100 * Exp(2, 16) + i * 2};
    }
  }

method CreateS2() returns (s2: set<nat32>) 
  {
    s2 := {};
    
    for i := 0 to 1000
    {
      s2 := s2 + {i * 31};
    }
    for i := 0 to 100
    {
      s2 := s2 + {5 * Exp(2, 16) + i};
    }
    for i := 0 to Exp(2, 15)
    {
      s2 := s2 + {100 * Exp(2, 16) + (i + 1) * 2};
    }
  }
  
  method Main() {
    var s1 := CreateS1();
    var s2 := CreateS2();
    var sUnion := s1 + s2;
  }