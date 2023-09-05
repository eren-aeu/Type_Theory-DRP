





--currying h: A → (B → C)
{-
g : ℕ → (ℕ → ℕ)
g = λ x → (λ y → x + y)


k : (ℕ → ℕ) → ℕ
k h = h 2 + h 3 -- neden ok kullanmadık?
-}

--polymorphic

variable
  A B C : Set

id : A → A
id x = x

--combinator

K : A → B → A
K x y = x

S : (A → B → C) → (A → B) → (A → C) -- what does that do
S f g x = f x (g x) 

-- every λ-term can be translated to S, K
-- combinatory logic

-- λ x = f x -- η-equality

{- if I do not comment out, it gives multiple definitions

A × B : Set
A ⊎ B : Set -- disjoint union

We dont have A ∪ B or A ∩ B . These are evil
opeartions since they depend on the elements!
-}

record _×_ (A B : Set) : Set where
  constructor _,_       
  field
    proj₁ : A
    proj₂ : B

open _×_



--when I press C-c C-d and write proj₁ it gives error. Instead it accepts _×_.proj₁ unlke the video 2
{-
_,_ : A → B → A × B
proj₁ (a , b) = a  -- copattern matching
proj₂ (a , b) = b --C-c C-s did not work, handwritten
-}
--copattern matching
--to define an element of a record, you need to define
-- what are its projections


curry : (A × B → C) → (A → B → C)
curry f a b = f(a , b)

uncurry :  (A → B → C) →  (A × B → C)
uncurry g x = g (proj₁ x) (proj₂ x)

--these two are inverses
--adjunction isomorphism, explains the relation btw functions and products
--functions are right adjoint to product


data _⊎_ (A B : Set) : Set where --iki fonksiyonla inşa ediliyor
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B 
  
-- sum, coproduct, disjoint union

case : (A → C) → (B → C) → (A ⊎ B → C)
case f g (inj₁ a) = f a --type x btw phrantesis then press C-c C-c
case f g (inj₂ b) = g b -- type C-c C- space to get rid of phrantesis

--uncurry case
uncase : (A ⊎ B → C) → (A → C) × (B → C)
proj₁ (uncase f) a  = f (inj₁ a)
proj₂ (uncase f) b = f (inj₂ b)
      
--also these two are inverses
-- they witness that ⊎ is a left-adjoint

--some terminology
--data is defined by consturctors _⊎_ , _×_
--codata (record) is defined by destructors _×_ , _→_ (functions) ,


--what do we do below??
{-
data _×'_ (A B : Set) : Set where
  _,_ : A → B → A ×' B

proj₁' : A ×' B → A
proj₁' (x , x₁) = x
-}
--proj₁' (a , b) = a --pattern matcing  (see copattern matching)

--binary products, sums
--nullary, empty product, sum??

record 𝕋 : Set where
  constructor tt

{-
tt : 𝕋
tt = record {}
-}

--the unit type, it has exactly one element tt
--() and ; are among key words

--NOTE: function arrows are right, operations are lef assc. (ℕ → (ℕ → ℕ) function of a first argument returns a function of second argument) --> Currying
-- this idea goes back to Frege (see plfa.github.io)


-- hole filling test with random operation #
--C-c C-l
--C-c C-c (and type m)
-- C-c C-,
--write a aterm inside a hole and press C-c C-space
--C-c C-r (refine) if there is  a unique constructor




data ⊥ : Set where  --empty type, no element

case⊥ : ⊥ → C
case⊥ () --impossible pattern

{-
prop = boolean, classical logic

mat is a creation of mind, it is difficult to say that propositions our mind created has a
truth value
-}

prop = Set --the type of evidence

variable
  P Q R : prop

infixl 5 _∧_
_∧_ : prop → prop → prop
P ∧ Q = P × Q --iki taraf ayı çalışıyor

infixl 3 _∨_
_∨_ : prop → prop → prop
P ∨ Q = P ⊎ Q

infixr 2 _⇛_
_⇛_ : prop → prop → prop
P ⇛ Q = P → Q

True : prop
True = 𝕋

False : prop
False = ⊥

¬ : prop → prop
¬ P = P ⇛ False

infix 1 _⇔_
_⇔_ : prop → prop → prop
P ⇔ Q = (P ⇛ Q) ∧ (Q ⇛ P)

--doğal gelecek şekilde tanımlıyoruz bağlaçları

deMorgan : ¬ (P ∨ Q) ⇔ ¬ P ∧ ¬ Q
proj₁ deMorgan = λ x → (λ x₁ → x (inj₁ x₁)) , (λ x₁ → x (inj₂ x₁)) --((P ⊎ Q) → False) → (P → False)×(Q → False)
proj₂ deMorgan (np , nq) (inj₁ x) = np x
proj₂ deMorgan (np , nq) (inj₂ x) = nq x --başardım :))
{-
proj₁ deMorgan x = (λ p → x (inj₁ p)) , λ q → x  (inj₂ q)  
proj₂ deMorgan y (inj₁ p) = proj₁ y p
proj₂ deMorgan y (inj₂ q) = proj₂ y q
-}
--in HoTT pro = hprop = types with at most one inhabitant (Set has more properties than prop, it is problamatic)--proof-irrelavant
-- excluded middle, tertium non datur (the third is not given)

TND : prop → prop
TND P = P ∨ ¬ P

--type theory ile cateogyleri tanımlayabiliri, tam tersi de doğru (o kadar geneller)
--fonkksiyonlar neden küme
--adjoint

deMorgan' : TND P → ¬ (P ∧ Q) ⇔ ¬ P ∨ ¬ Q
proj₁ (deMorgan' (inj₁ p)) h = inj₂ (λ q → h (p , q))  --şu anda inj\_1 yazamıyorum
proj₁ (deMorgan' (inj₂ np)) h = inj₁ np
proj₂ (deMorgan' _) (inj₁ np) (p , q) = np p
proj₂ (deMorgan' _)  (inj₂ np) (p , q) = np q  -- alt tire neden(kanıtta kullanamdık)


RAA : prop → prop --redutio ad absurdum
RAA P = ¬(¬ P) → P --parantez olmayınca çalışmadı


--raa is not provable in int. logic
--let us first prove tnd implies raa

tnd→raa : TND P → RAA P
tnd→raa (inj₁ p) nnp = p
tnd→raa (inj₂ np) nnp = case⊥ (nnp np)

{-
raa→tnd : RAA P → TND P
is not provable
we need extra assumption
-}

nntnd : ¬ (¬ (P ∨ ¬ P))
nntnd h = h (inj₂ (λ p → h (inj₁ p)))

raa→tnd : ({P : prop} →  RAA P) → {Q : prop} → TND Q
raa→tnd raa = raa nntnd


-------


data ℕ : Set where
 zero : ℕ
 suc : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc one

{-# BUILTIN NATURAL ℕ #-}


_+_ : ℕ → ℕ → ℕ
zero + n = n -- ilk başta m + n = ? yaz, boşluğa m yaz sonra C-c C-c
suc m + n = suc (m + n)

--structural recursive definition
{-
_+'_ : ℕ → ℕ → ℕ
zero +' n = {!n!}
suc n +' m = suc n +' m
-}


_#_ : ℕ → ℕ → ℕ
a # b 