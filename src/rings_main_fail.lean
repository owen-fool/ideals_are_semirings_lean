universe u

def has_ring_structure (X : Type u) :=
  (X → X → X) × (X → X → X) × X × X × (X → X)

def plus (X : Type u) (S : has_ring_structure X) :=
  S.1

def mult (X : Type u) (S : has_ring_structure X) :=
  S.2.1

def zero (X : Type u) (S : has_ring_structure X) :=
  S.2.2.1

def one (X : Type u) (S : has_ring_structure X) :=
  S.2.2.2.1

def inv (X : Type u) (S : has_ring_structure X) :=
  S.2.2.2.2

def is_ring (X : Type u) (S : has_ring_structure X) :=
  ( (∀ (x y z : X), plus X S x (plus X S y z) 
                  = plus X S (plus X S x y) z)
  ∧ (∀ (x y : X),   plus X S x y           = plus X S y x)
  ∧ (∀ (x : X),     plus X S (zero X S) x  = x)
  ∧ (∀ (x : X),     plus X S x (inv X S x) = zero X S)
  ∧ (∀ (x y z : X), mult X S x (mult X S y z) 
                  = mult X S (mult X S x y) z)
  ∧ (∀ (x : X),     mult X S (one X S) x   = x 
                ∧   mult X S x (one X S)   = x)
  ∧ (∀ (x y z : X), mult X S x (plus X S y z) 
                  = plus X S (mult X S x y) (mult X S x z)
                ∧   mult X S (plus X S x y) z
                  = plus X S (mult X S x z) (mult X S y z)))
-- how to make this more readable?

def plus_assoc (X : Type u) (S : has_ring_structure X)
               (R : is_ring X S)                      :=
  R.1

def plus_comm (X : Type u) (S : has_ring_structure X)
              (R : is_ring X S)                      :=
  R.2.1

def plus_ident (X : Type u) (S : has_ring_structure X)
               (R : is_ring X S)                      :=
  R.2.2.1

def plus_inv (X : Type u) (S : has_ring_structure X)
             (R : is_ring X S)                      :=
  R.2.2.2.1

def mult_assoc (X : Type u) (S : has_ring_structure X)
               (R : is_ring X S)                      :=
  R.2.2.2.2.1

def mult_ident (X : Type u) (S : has_ring_structure X)
               (R : is_ring X S)                      :=
  R.2.2.2.2.2.1

def distributivity (X : Type u) (S : has_ring_structure X)
                   (R : is_ring X S)                      :=
  R.2.2.2.2.2.2 

structure Ring :=
  (X : Type u)
  (S : has_ring_structure X)
  (R : is_ring X S)

def is_embedding (X Y : Type u) (f : X → Y) : Prop :=
  ∀ (x x' : X), f x = f x' → x = x'

def sub (R : Ring) : R.X → R.X → R.X :=
  λ x, λ y, plus R.X R.S x (inv R.X R.S y)

structure sub_set (R : Ring) :=
  (Y : R.X → Prop)

structure Subring (R : Ring) extends sub_set R :=
  (closed_under_sub  : ∀ (x y : R.X), Y x → Y y → Y (sub R x y))
  (closed_under_mult : ∀ (x y : R.X), Y x → Y y → Y (mult R.X R.S x y)) -- i don't think we need to explicitly include a two-sidedness clause here

structure Ideal (R : Ring) extends Subring R :=
  (left_ideal  : ∀ (x y : R.X), Y x → Y (mult R.X R.S y x))
  (right_ideal : ∀ (x y : R.X), Y x → Y (mult R.X R.S x y))

def z_prod_sum (R : Ring) (I I' : Ideal R) (z :)

def num_prod_sum (R : Ring) (I I' : Ideal R) (z : R.X) : ℕ → Prop
  | 0 := true
  | 1 := ∃ (x y : R.X), I.Y x ∧ I'.Y y ∧ z = (mult R.X R.S x y)
  | (nat.succ n) := ∃ (x y : R.X), I.Y x ∧ I'.Y y ∧ (num_prod_sum )
