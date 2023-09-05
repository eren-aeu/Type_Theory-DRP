{-
DRP-Turkey 2023
Mentee: Adem Eren Uyanık
Mentor: Elif Üsküplü
Title: What Is Type Theory and Why Should We Care About It?

-----------------------------------------------------------------------------------
What is type theory:


*Per Martin-Löf's type theory 

*Every object comes within a type 

  term : TYPE
  ---------------
  0    : ℕ
  true : bool
  f    : ℕ → ℕ
  ...

*Definition: A formal language, a set of rules for writing certain strings 
of symbols, which describes the introduction of types and 
their terms, and computation with them in a "meaningful" way.

*Implementation of logic
  - P or Q = P ⊎ Q
  - P ⇛ Q = P → Q
    
---------------------------------------------------------------------------
Why type theory:

*Alternative foundation for mathematics

*Forced to use sets:
  -1 ⊂ 2 (von Nuemann)
  -Function is a set??
  -Type theory helps us hide these strange side effects

*A practical problem: proof checking.
  -Mathematicians are only human after all 

*Curry-Howard Isomorphism: Propositions as types! 
  --> extracting computer proofs from human proofs.
  - ProofofModusPonens : (P ⇛ Q) ∧ P ⇛ Q
  - ProofofModusPonens = ... (a well-typed expression)
-}
---------------------------------------------------------------------------------

--Agda, a proof assistant
--Note: In order for this file to be compiled some changes (commenting necessary parts out and infxl notation) must be made.


data ℕ : Set where  --Set = set of all mathematical objects in Agda, just a naming
 zero : ℕ
 suc : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc one

_+_ : ℕ → ℕ → ℕ
zero + n = n 
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = (m * n) + n



variable
  A B C : Set


{-
A ∩ B : Set
  x ∈ A and x ∈ B

-- 4 rules to create a new type
1. Formation rule -- how to form a new type
2. Introduction rule -- how to construct elements of the type
3. Elimination (induction) rule -- how to use elements of the type
4. Computation rule -- how the elimination rule acts on introduction rule
-}


--product type

record _×_ (A B : Set) : Set where
  constructor _,_       
  field 
    proj₁ : A
    proj₂ : B  
open _×_

--Eliminition (induction): If I want to write f : A × B → C, then all
I have to do is to define f(a,b).

--Computation: proj₁(a,b) = a, proj₂(a,b) = b.


--coproduct type, disjoint sum (a term comes exactly from one)

data _⊎_ (A B : Set) : Set where 
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B 



--the unit type, it has exactly one element tt

record 𝕋 : Set where
  constructor tt



--empty type, no element

data ⊥ : Set where  


---------------------------------------------------------------------------------
--Logic


prop = Set 

variable
  P Q R : prop

  
_∧_ : prop → prop → prop   
P ∧ Q = P × Q 


_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q  


_⇛_ : prop → prop → prop
P ⇛ Q = P → Q  
-- a term of P ⇛ Q is a function transforming a 
--proof of P to a proof of Q


True : prop
True = 𝕋 --by definition non-empty (hence true)


False : prop
False = ⊥ --empty (hence false)


¬ : prop → prop
¬ P = P ⇛ False --if while ¬ P is true, P is true; then there is a term of False!


_⇔_ : prop → prop → prop
P ⇔ Q = (P ⇛ Q) ∧ (Q ⇛ P)


-- a proof without truth tables

-- MODUS PONENS --
--Step 1
MP : (P ⇛ Q) ∧ P ⇛ Q
MP = ?
--Agda Says "? : (P ⇛ Q) ∧ P ⇛ Q" since this is a function type we need 
--to supply an argument first

--Step 2
MP : (P ⇛ Q) ∧ P ⇛ Q
MP x = ?
--Agda says "? : Q" because we already supplied "x : (P ⇛ Q) ∧ P",
--Agda also says "x must be of the form (_,_) where the first comes from 
-- (P ⇛ Q), the second from P"

--Step 3
MP : (P ⇛ Q) ∧ P ⇛ Q
MP (f , p) = ?
--Well, we changed x in a right pattern, and Agda says "f :  (P ⇛ Q),
-- p : P, and we need ? : Q"

--Step 4
MP : (P ⇛ Q) ∧ P ⇛ Q
MP (f , p) = f p 
--Agda says "we are done" because (f p) is a term in Q.



-- not a magic (?), just definitions and Curry-Howard Isomorphism!



deMorgan : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q

--(⇛) assume ¬ (P ∨ Q) show ¬ P ∧ ¬ Q    
proj₁ (proj₁ deMorgan f) p = f (inj₁ p) 
proj₂ (proj₁ deMorgan f) q = f (inj₂ q)

--(⇐) assume ¬ P ∧ ¬ Q show  ¬ (P ∨ Q)
proj₂ deMorgan (np , nq) (inj₁ x) = np x
proj₂ deMorgan (np , nq) (inj₂ x) = nq x


-- Axiomatisation in Type Theory:
-- Law of excluded middle, tertium non datur (the third is not given)

TND : prop → prop
TND P = P ∨ ¬ P
 








