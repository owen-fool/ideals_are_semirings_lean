universe u

variable X    : Type u

variable f    : X → X → X

variable g    : X → X → X

variable e    : X

variable a    : ∀ x y z : X, f x (f y z) = f (f x y) z

variable a'   : ∀ x y : X, f x y = f y x

variable a''  : ∀ x : X, f e x = x

variable finv : ∀ x : X, X

variable a''' : ∀ x : X, f x (finv x) = e

variable e'   : X

variable b    : ∀ x y z : X, g x (g y z) = g (g x y) z

variable b''  : ∀ x : X, g e' x = x ∧ g x e' = x

variable c    : ∀ x y z : X, g x (f y z) = f (g x y) (g x z) 
                           ∧ g (f x y) z = f (g x z) (g y z)

def X_ring_structure := (X , f , g , e , e', finv)



def X_ring_axioms    := and.intro a (and.intro a' (and.intro a'' 
                                    (and.intro a''' (and.intro b 
                                    (and.intro b'' c)))))



include X f g finv

include a' a''
lemma add_id_is_unique : ∀ e'' : X, (∀ x : X, f e'' x = x) → e'' = e :=
begin
  intros e'' h,
  calc
    e''     = f e e'' : by { symmetry, exact a'' e'' }
        ... = f e'' e : by exact a' e e''
        ... = e       : by exact h e,
end

include a a'''
lemma add_inv_is_unique : ∀ x y : X, f x y = e → y = finv x :=
begin
  intros x y h,
  calc
    y     = f e y              : by { symmetry, exact a'' y }
      ... = f (f x (finv x)) y : by { symmetry, rw a''' x }
      ... = f (f (finv x) x) y : by { rw a' x (finv x) }
      ... = f (finv x) (f x y) : by { symmetry, exact a (finv x) x y}
      ... = f (finv x) e       : by rw h
      ... = f e (finv x)       : by exact a' (finv x) e
      ... = finv x             : by exact a'' (finv x),
end

include e' b b''
lemma mul_lid_is_unique : ∀ e'' : X, (∀ x : X, g e'' x = x) → e'' = e' :=
begin
  intros e'' h,
  calc
    e''     = g e'' e' : by { symmetry, exact (b'' e'').2 }
        ... = e'       : by exact h e',
end

lemma mul_rid_is_unique : ∀ e'' : X, (∀ x : X, g x e'' = x) → e'' = e' :=
begin
  intros e'' h,
  calc
    e''     = g e' e'' : by { symmetry, exact (b'' e'').1 }
        ... = e'       : by exact h e',
end

include c
lemma mul_zero_left : ∀ x : X, g e x = e :=
begin
  intro x,
  -- proof i found on wikipedia
  calc
    g e x     = f e (g e x)                          : by { symmetry, exact a'' (g e x) }
          ... = f (g e x) e                          : by { symmetry, exact a' (g e x) e }
          ... = f (g e x) (f (g e x) (finv (g e x))) : by { symmetry, rw a''' (g e x) }
          ... = f (f (g e x) (g e x)) (finv (g e x)) : by exact a (g e x) (g e x) (finv (g e x))
          ... = f (g (f e e) x) (finv (g e x))       : by { symmetry, rw (c e e x).2 }
          ... = f (g e x) (finv (g e x))             : by rw a'' e
          ... = e                                    : by exact a''' (g e x),
end

lemma mul_zero_right : ∀ x : X, g x e = e :=
begin
  intro x,
  -- substantially the same as the above
  calc
    g x e     = f e (g x e)                          : by { symmetry, exact a'' (g x e) }
          ... = f (g x e) e                          : by exact a' e (g x e)
          ... = f (g x e) (f (g x e) (finv (g x e))) : by { symmetry, rw a''' (g x e)}
          ... = f (f (g x e) (g x e)) (finv (g x e)) : by exact a (g x e) (g x e) (finv (g x e))
          ... = f (g x (f e e)) (finv (g x e))       : by { symmetry, rw (c x e e).1 }
          ... = f (g x e) (finv (g x e))             : by rw a'' e
          ... = e                                    : by exact a''' (g x e),
end


lemma mul_inv_one_inv_left : ∀ x : X, g (finv e') x = finv x :=
begin
  intro x,
  apply add_inv_is_unique,
  { exact f },
  { exact a },
  { exact a' },
  { exact a'' },
  { exact a''' },
  -- there should be an easier way to bring in all those assumptions
  calc
    f x (g (finv e') x)     = f (g e' x) (g (finv e') x) : by { symmetry, rw (b'' x).1 }
                        ... = g (f e' (finv e')) x       : by { symmetry, exact (c e' (finv e') x).2 }
                        ... = g e x                      : by rw a''' e'
                        ... = e                          : by { exact mul_zero_left X f g e a a' a'' finv a''' e' b b'' c x }, --screaming
end

lemma mul_inv_one_inv_right : ∀ x : X, g x (finv e') = finv x :=
begin
  intro x,
  apply add_inv_is_unique,
  { exact f },
  { exact a },
  { exact a' },
  { exact a'' },
  { exact a''' },
  calc
    f x (g x (finv e'))     = f (g x e') (g x (finv e')) : by { symmetry, rw (b'' x).2 }
                        ... = g x (f e' (finv e'))       : by { symmetry, exact (c x e' (finv e')).1 }
                        ... = g x e                      : by rw a''' e'
                        ... = e                          : by { exact mul_zero_right X f g e a a' a'' finv a''' e' b b'' c x },
end

-- i would also like to prove the binomial theorem, but i'll leave that for now