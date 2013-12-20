newPackage(
	"Decompositions",
    	Version => "0.2", 
    	Date => "December 20, 2013",
    	Authors => {
	     {Name => "Branden Stone", Email => "bstone@bard.edu", HomePage => "http://math.bard.edu/~bstone"},
	     {Name => "Courtney Gibbons", Email => "s-cgibbon5@math.unl.edu", HomePage => "http://www.math.unl.edu/~s-cgibbon5/"}
	     },
    	Headline => "Decompositions",
    	DebuggingMode => true
    	)

export {
     -- Methods
     --"makeCI",
     "pureBettiHK",
     "pureBettiDiagramHK",
     "pureDegreesHK",
     "decomposeHK",
     "decomposeDegreesHK",
     "pureBettiES",
     "pureBettiDiagramES",
     "pureDegreesES",
     "decomposeES",
     "decomposeDegreesES",
     "pureDegrees",
     "massExtinction",
     "bettiDeath",
     "degreeDiff",
     "bettiDEATH",
     
     -- Options
     "VariableName",
     "DeathSequence"

}

needsPackage("BoijSoederberg");

----------------------------------------------------------------------
-- New Types
----------------------------------------------------------------------
BettiDeathTally = new Type of BettiTally;
BettiEliminationTally = new Type of BettiTally;


---Helper functions (you should ignore these)
isStrictlyIncreasing = method();
isStrictlyIncreasing List := L -> (
     t:=true;
     for i from 0 to #L-2 do t=(t and (L_i<L_(i+1)));
     t)

--Input: Degs must be a strictly increasing list of positive integers
--Output: List of theoretical rational Betti numbers resulting from the Herzog-Kuhl equations
pureBettiHK = method()
pureBettiHK List := (degs) -> (
     codim := #degs;
     for i from 0 to codim-1 list
     (
	  1/(product(for j from 0 to i-1 list degs#i-degs#j) * product(for j from i+1 to codim-1 list degs#j-degs#i))
	  )
     )


pureBettiDiagramHK = method()
pureBettiDiagramHK List := (degs) -> (
     B := pureBettiHK degs;
     new BettiTally from apply(#degs, i -> (i, {degs#i}, degs#i) => B#i)
     )

decompose1 = method();
decompose1 BettiTally := B -> (
     L:=lowestDegrees B;
     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     C:=pureBettiDiagramHK L;
     ratio:=min apply(#L, i->(B#(i,{L_i}, L_i))/(C#(i,{L_i},L_i)));
     (C,ratio,merge(B,C, (i,j)->i-ratio*j))
     )

pureBettiES = method()
pureBettiES List := (degs) -> (
     codim := #degs;
     L := for i from 1 to codim-1 list
     (
	 binomial(degs#i -1,degs#i-degs#(i-1) - 1)
	 );
     b0 := (product L)*(1/(pureBettiDiagramHK(degs))#((0,{0},0)));
     for i from 0 to codim-1 list
     (
	  b0/(product(for j from 0 to i-1 list degs#i-degs#j) * product(for j from i+1 to codim-1 list degs#j-degs#i))
	  )
)

pureBettiDiagramES = method()
pureBettiDiagramES List := (degs) -> (
     B := pureBettiES degs;
     new BettiTally from apply(#degs, i -> (i, {degs#i}, degs#i) => B#i)
     )

decompose2 = method();
decompose2 BettiTally := B -> (
     L:=lowestDegrees B;
     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     C:=pureBettiDiagramES L;
     ratio:=min apply(#L, i->(B#(i,{L_i}, L_i))/(C#(i,{L_i},L_i)));
     (C,ratio,merge(B,C, (i,j)->i-ratio*j))
     )

---Methods for general use---

---Input: pure Betti table
---Output: degree sequence (or an error if the diagram isn't pure)
pureDegrees = method();
pureDegrees BettiTally := B -> (
     if lowestDegrees(B)==highestDegrees(B) then return highestDegrees(B)
     else return "Error: diagram is not pure."
     )

---Input: Betti table (eg, betti res M for a module M)
---Output: Sum of the pure diagrams as defined in Dan's lectures (with fractions from the H-K equations)
decomposeHK = method();
decomposeHK BettiTally := B-> (
     Components:={};
     B1:= new MutableHashTable from B;
     while min values B1 >= 0 and max values B1 > 0 do (
	  X:=decompose1(new BettiTally from B1);
	  B1=new MutableHashTable from X_2;
	  --change the type of the values in X_0 to ZZ
	  Y:=new BettiTally from apply(pairs X_0, i->{first i,last i});
	  Components = append(Components, hold(X_1) * Y));
     sum Components
     )

---Input: Betti table
---Output: List of the coefficients with the pure degree sequences from above
decomposeDegreesHK = method();
decomposeDegreesHK BettiTally := B-> (
     Components:={};
     B1:= new MutableHashTable from B;
     while min values B1 >= 0 and max values B1 > 0 do (
	  X:=decompose1(new BettiTally from B1);
	  B1=new MutableHashTable from X_2;
	  --change the type of the values in X_0 to ZZ
	  Y:=new BettiTally from apply(pairs X_0, i->{first i, last i});
	  Components = append(Components, (X_1,pureDegrees(Y))));
     Components
     )

---Input: Betti table (eg, betti res M for a module M)
---Output: Sum of the pure diagrams as defined in Dan's lectures (with fractions from the E-S existence proof)
decomposeES = method();
decomposeES BettiTally := B-> (
     Components:={};
     B1:= new MutableHashTable from B;
     while min values B1 >= 0 and max values B1 > 0 do (
	  X:=decompose2(new BettiTally from B1);
	  B1=new MutableHashTable from X_2;
	  --change the type of the values in X_0 to ZZ
	  Y:=new BettiTally from apply(pairs X_0, i->{first i,last i});
	  Components = append(Components, hold(X_1) * Y));
     sum Components
     )

decomposeDegreesES = method();
decomposeDegreesES BettiTally := B -> (
     Components:={};
     B1:= new MutableHashTable from B;
     while min values B1 >= 0 and max values B1 > 0 do (
	  X:=decompose2(new BettiTally from B1);
	  B1=new MutableHashTable from X_2;
	  --change the type of the values in X_0 to ZZ
	  Y:=new BettiTally from apply(pairs X_0, i->{first i, last i});
	  Components = append(Components, (X_1,pureDegrees(Y))));
     Components
     )
     
     
--  input:  BettiTally of a Cohen-Macaulay Module
-- output:  Boolean Value, True if more than one betti dies in the
--     	    decompose algorithm     	    
-- caveat:  Prints a warning if not the "Generic Case"
massExtinction = method();
massExtinction BettiTally :=  B -> (
      local SCAN; local D; local LD;
            
      scan( values B, i -> if i != 1 then break print "-- Warning: Not Generic Case");
      
      D = decomposeDegreesHK B;
      LD = apply(#D-1, i-> D#(i+1)#1-D#i#1 );
      
      SCAN = scan( LD, l -> if #positions( l, i -> i != 0 ) != 1 then break "true" );
      if SCAN === null
      then return false 
      else return true;
     )

--  input:  BettiTally of a Cohen-Macaulay Module
--     	    Cohen-Macualay Ideal
-- output:  List, if no mass elimination occors, a list is given sequencing
--     	    the homological degree of the elimination of betti numbers
-- options: EliminationSequence => Boolean; default is false, thus the output is 
--     	    a BettiTally.  If true, only the EliminationSequence is returned.
bettiDeath = method(Options =>{DeathSequence => false});
bettiDeath BettiTally := o -> B -> (
     local D; local LD;
     local C;local L; local LL; local P; local K; local p; local c;
     
     if massExtinction(B) == true then print"\n --MASS EXTINCTION!--";
     
     D = decomposeDegreesHK B;
     LD = apply(#D-1, i-> D#(i+1)#1-D#i#1 );
     
     if o.DeathSequence == true then return apply( LD, l -> positions( l, i -> i != 0) );
     
     c = pdim B;
     p = #D;
               
     C = new MutableHashTable from B;
     
     L = prepend( {p}, bettiDeath( B, DeathSequence => true ) );
     LL = apply(c, j -> positions(L, l ->  any( l, i -> i == j  )  ) );
     P = flatten append( prepend ( p, apply(1..(#LL-1), i ->  append(LL#i, p ) ) ), p );
     K = sort keys C;
     scan(#P, i -> C#(K#i) = P#i );
     return new BettiEliminationTally from C;
    )

bettiDeath Ideal := o -> I -> (
     return bettiDeath( betti res I, DeathSequence => o.DeathSequence );
     )
 
--  input: List of degrees (type of an artinian complete intersection)
--  output: BettiTally of such a complete intersection
makeCI = method(Options=>{VariableName=>getSymbol "tt"});
makeCI List := opts -> degs ->  (
     c := #degs; 
     tt := opts.VariableName;
     S := ZZ/499[tt_1..tt_c];
     G := toSequence(for i from 0 to (c-1) list S_i^(degs#i));
     I := ideal G;
     betti res (S^1/G)
     )

--  input:  BettiTally of a Cohen-Macaulay Module
-- output:  List, differnce of degree sequence in decomposeDegreesHK
degreeDiff = method();
degreeDiff BettiTally := B -> (
     local D; 
     D = decomposeDegreesHK B;
     return apply(#D-1, i-> D#(i+1)#1-D#i#1 );
)

end

---EXAMPLES---
loadPackage "BoijSoederberg"
S = ZZ/101[x,y,z]
M = S^1/ideal(x^2,y^2,z^2)
isPure betti res M
pureDegrees(betti res M)
decomposeHK(betti res M)
decomposeDegrees(betti res N)

N = M ++ S^1/ideal(x,y,z^3)
isPure betti res N
pureDegrees(betti res N)
decomposeHK(betti res N)
decomposeDegrees(betti res N)

restart
makeCI {2,2,8}


-- Home of bettiDEATH
bettiDEATH = method();
bettiDEATH List := L -> (
     L={};
     return"   ,-------------.	\n  /               \\	\n /   __       __   \\	\n|  /,--.     ,--.\\  |	     \n|   \\  |  __ |  /   |     \n|    `-' /  \\`-/    |     \n \\__    |_/\\_|   __/     \n   /_           _\\	     \n   |B|,-.,-.,-.|I|	     \n   `-'|E||T||T|`-'	     \n   ,-.`-'`-'`-',-.	     \n   \\_|_,-.,-.,-|_/	     \n   | |_|_||_||_|   	     \n    `--______--'  	     ";
     )
