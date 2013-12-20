newPackage(
	"Decompositions",
    	Version => "0.2", 
    	Date => "December 20, 2013",
    	Authors => {
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
	     {Name => "Branden Stone", Email => "bstone@bard.edu", HomePage => "http://math.bard.edu/~bstone"},
	     {Name => "Courtney Gibbons", Email => "crgibbon@hamilton.edu", HomePage => "http://people.hamilton.edu/cgibbons"}
=======
=======
>>>>>>> f2bc2c3df670d7204484a8162d89d3370d25763d
=======
>>>>>>> f2bc2c3df670d7204484a8162d89d3370d25763d
	     {Name => "Branden Stone", Email => "bstone@bard.edu", HomePage => "http://math.bard.edu/~bstone/"},
	     {Name => "Courtney Gibbons", Email => "s-cgibbon5@math.unl.edu", HomePage => "http://www.math.unl.edu/~s-cgibbon5/"}
>>>>>>> f2bc2c3df670d7204484a8162d89d3370d25763d
	     },
    	Headline => "Decompositions",
    	DebuggingMode => true
    	)

export {
     -- Methods
     --"makeCI",
     "makePureBettiHK",
     "makePureBettiDiagramHK",
     "makePureDegreesHK",
     "decomposeHK",
     "decomposeDegreesHK",
     "makePureBettiES",
     "makePureBettiDiagramES",
     "makePureDegreesES",
     "decomposeES",
     "decomposeDegreesES",
     "listPureDegrees",
     "isMassEliminate",
     "eliminateBetti",
     "degreeDiff",
--     "bettiDEATH",
     
     -- Options
     "VariableName",
     "EliminationSequence"

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

--  input: List consisting of strictly increasing list of positive integers 
--         (a degree sequence)
-- output: List of theoretical rational Betti numbers resulting from the 
--         Herzog-Kuhl equations
makePureBettiHK = method()
makePureBettiHK List := (degs) -> (
     codim := #degs;
     for i from 0 to codim-1 list
     (
	  1/(product(for j from 0 to i-1 list degs#i-degs#j) * product(for j from i+1 to codim-1 list degs#j-degs#i))
	  )
     )

--  input: List consisting of strictly increasing list of positive integers 
--         (a degree sequence)
-- output: BettiTally with the theoretical rational Betti numbers resulting from
--         the Eisenbud-Schreyer constructions
    
makePureBettiDiagramHK = method();
makePureBettiDiagramHK List := (degs) -> (
     B := makePureBettiHK degs;
     new BettiTally from apply(#degs, i -> (i, {degs#i}, degs#i) => B#i)
     )

-- This helper method is used to compute...
--  input:
-- output:
decompose1 = method();
decompose1 BettiTally := B -> (
     L:=lowestDegrees B;
     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     C:=makePureBettiDiagramHK L;
     ratio:=min apply(#L, i->(B#(i,{L_i}, L_i))/(C#(i,{L_i},L_i)));
     (C,ratio,merge(B,C, (i,j)->i-ratio*j))
     )

--  input: List (a degree sequence)
-- output: List (a list of the number of generators of the realization module
--         in each degree)
makePureBettiES = method()
makePureBettiES List := (degs) -> (
     codim := #degs;
     L := for i from 1 to codim-1 list
     (
	 binomial(degs#i -1,degs#i-degs#(i-1) - 1)
	 );
     tag := first sort keys makePureBettiDiagramHK(degs);
     b0 := (product L)*(1/(makePureBettiDiagramHK(degs))#tag);
     --returns an error if the first degree is not 0. need to fix.
     for i from 0 to codim-1 list
     (
	  b0/(product(for j from 0 to i-1 list degs#i-degs#j) * product(for j from i+1 to codim-1 list degs#j-degs#i))
	  )
)

--  input: List (a degree sequence)
-- output: BettiTally (the Betti table of the realization module
--         for the given degree sequence)
makePureBettiDiagramES = method()
makePureBettiDiagramES List := (degs) -> (
     B := makePureBettiES degs;
     new BettiTally from apply(#degs, i -> (i, {degs#i}, degs#i) => B#i)
     )

-- this helper method is used to compute...
--  input:
-- output:
decompose2 = method();
decompose2 BettiTally := B -> (
     L:=lowestDegrees B;
     if not isStrictlyIncreasing L then print "NOT IN THIS SIMPLEX OF PURE BETTI DIAGRAMS";
     C:=makePureBettiDiagramES L;
     ratio:=min apply(#L, i->(B#(i,{L_i}, L_i))/(C#(i,{L_i},L_i)));
     (C,ratio,merge(B,C, (i,j)->i-ratio*j))
     )

---Methods for general use---

--  input: pure Betti table
-- output: degree sequence (or an error if the diagram isn't pure)
listPureDegrees = method();
listPureDegrees BettiTally := B -> (
     if lowestDegrees(B)==highestDegrees(B) then return highestDegrees(B)
     else return "Error: diagram is not pure."
     )

--  input: Betti table (eg, betti res M for a module M)
-- output: Sum of the pure diagrams as defined in Dan's lectures 
--         (with fractions from the H-K equations)
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

--  input: Betti table
-- output: List of the coefficients with the pure degree sequences from above
decomposeDegreesHK = method();
decomposeDegreesHK BettiTally := B-> (
     Components:={};
     B1:= new MutableHashTable from B;
     while min values B1 >= 0 and max values B1 > 0 do (
	  X:=decompose1(new BettiTally from B1);
	  B1=new MutableHashTable from X_2;
	  --change the type of the values in X_0 to ZZ
	  Y:=new BettiTally from apply(pairs X_0, i->{first i, last i});
	  Components = append(Components, (X_1,listPureDegrees(Y))));
     Components
     )

--  input: Betti table (eg, betti res M for a module M)
-- output: Sum of the pure diagrams as defined in Dan's lectures (with fractions from the E-S existence proof)
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
	  Components = append(Components, (X_1,listPureDegrees(Y))));
     Components
     )
     
     
--  input:  BettiTally of a Cohen-Macaulay Module
-- output:  Boolean Value, True if more than one betti dies in the
--     	    decompose algorithm     	    
-- caveat:  Prints a warning if not the "Generic Case"
isMassEliminate = method();
isMassEliminate BettiTally :=  B -> (
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
eliminateBetti = method(Options =>{EliminationSequence => false});
eliminateBetti BettiTally := o -> B -> (
     local D; local LD;
     local C;local L; local LL; local P; local K; local p; local c;
     
     if isMassEliminate(B) == true then print"\n --MASS EXTINCTION!--";
     
     D = decomposeDegreesHK B;
     LD = apply(#D-1, i-> D#(i+1)#1-D#i#1 );
     
     if o.EliminationSequence == true then return apply( LD, l -> positions( l, i -> i != 0) );
     
     c = pdim B + 1;
     p = #D;
               
     C = new MutableHashTable from B;
     
     L = prepend( {p}, eliminateBetti( B, EliminationSequence => true ) ); 
     LL = apply(c, j -> positions(L, l ->  any( l, i -> i == j  )  ) );
     P = flatten prepend ( p, apply(1..(#LL-1), i ->  append(LL#i, p ) ) );
     if last LL == {0} then P = delete(0,P);
     K = sort keys C;
     scan(#P, i -> C#(K#i) = P#i );
     return new BettiEliminationTally from C;
    )

eliminateBetti Ideal := o -> I -> (
     return eliminateBetti( betti res I, EliminationSequence => o.EliminationSequence );
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


beginDocumentation();
needsPackage "SimpleDoc"
debug SimpleDoc

doc ///
    Key
    	Decompositions
    Headline
    	Decompositions of Betti Diagrams with different conventions
    Description
    	Text
	    This patch allows users to specify a decomposition into pure
	    diagrams according to different conventions.  These conventions
	    are: ...
///

doc ///
    Key
    	makePureBettiHK
	(makePureBettiHK,List)
    Headline
        Pure Diagram with theoretical entries.
    Usage
    	makePureBettiDiagramHK(L)
    Inputs
    	L:List
	    List of integers {d_1,...,d_n} such that d_i < d_{i+1} for each i
    Outputs
    	D:List
	    A list of each (i,d_i)-th theoretical Betti number.
    Description
    	Text
	    The list returned records the entries in the Betti diagram
	    that are calculated according to the formula given in the first 
	    Boij-Soederberg paper, where each entry is calculated using the 
	    Herzog-Kuhl equations for the free resolutions of pure Cohen-Macaulay
	    modules.
    	Example
	    makePureBettiHK({0,2,3})
///
	    
doc ///
    Key
    	makePureBettiDiagramHK
	(makePureBettiDiagramHK,List)	
    Headline
        Pure Diagram with theoretical entries.
    Usage
    	makePureBettiDiagramHK(L)
    Inputs
    	L:List
	    List of integers {d_1,...,d_n} such that d_i < d_{i+1} for each i
    Outputs
    	B:BettiTally
	    A Betti diagram with theoretical (possibly fractional entries)
	    governed by the Herzog-Kuhl equation.
    Description
    	Text
	    The Betti diagram returned has entries that are calculated according
	    to the formula given in the first Boij-Soederberg paper, where each
	    entry is calculated using the Herzog-Kuhl equations for the free resolutions
	    of pure Cohen-Macaulay modules.
    	Example
	    makePureBettiDiagramHK({0,2,3})
///

doc ///
    Key
    	makePureBettiES
	(makePureBettiES,List)
    Headline
        Pure Diagram with theoretical entries.
    Usage
    	makePureBettiDiagramES(L)
    Inputs
    	L:List
	    List of integers {d_1,...,d_n} such that d_i < d_{i+1} for each i
    Outputs
    	D:List
	    A list of each (i,d_i)-th theoretical Betti number.
    Description
    	Text
	    The list returned records the Betti numbers
	    of the realization module for the input degree sequence, as
	    constructed by Eisenbud and Schreyer.
    	Example
	    makePureBettiES({0,2,3})
///
	    
doc ///
    Key
    	makePureBettiDiagramES
	(makePureBettiDiagramES,List)	
    Headline
        Pure Diagram of a CM realization module.
    Usage
    	makePureBettiDiagramES(L)
    Inputs
    	L:List
	    List of integers {d_1,...,d_n} such that d_i < d_{i+1} for each i
    Outputs
    	B:BettiTally
	    A Betti diagram with actual Betti 
    Description
    	Text
	    The Betti diagram returned has entries that are the Betti numbers
	    of the realization module for the input degree sequence, as
	    constructed by Eisenbud and Schreyer.
    	Example
	    makePureBettiDiagramES({0,2,3})
///


end

---EXAMPLES---
loadPackage "BoijSoederberg"
S = ZZ/101[x,y,z]
M = S^1/ideal(x^2,y^2,z^2)
isPure betti res M
listPureDegrees(betti res M)
decomposeHK(betti res M)
decomposeDegrees(betti res N)

N = M ++ S^1/ideal(x,y,z^3)
isPure betti res N
listPureDegrees(betti res N)
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



