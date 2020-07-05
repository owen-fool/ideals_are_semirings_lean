/-- These are lemmas i found myself proving in the course of producing full_proof, i am aware that
    there is heavy redundency -/

lemma lt_irrfl : ∀ n : ℕ, ¬ n < n :=
begin
 intro n,
 induction n with n hn,
 { intro hz, cases hz with r hr, },
 { intro h,
   apply hn,
   exact nat.lt_of_succ_lt_succ h, },
end

lemma add_succ_commute : ∀ m n : ℕ, nat.add m (nat.succ n) = nat.succ (nat.add m n) :=
begin
 intros m n,
 exact rfl,
end

lemma add_succ_commute' : ∀ m n : ℕ, nat.add (nat.succ m) n = nat.succ (nat.add m n) :=
begin
 intros m n,
 exact nat.succ_add m n,
end

-- i think this one could be tidied up
lemma lt_succ_add : ∀ m n : ℕ, m < nat.succ (nat.add m n) :=
begin
 intros m n,
 apply nat.lt_succ_of_le,
 induction n with n hn,
 { have h : nat.add m 0 = m,
   { exact nat.add_zero m, },
   apply nat.le_of_eq,
   rw h, },
 { calc
    m     ≤ nat.add m n : by exact hn
      ... ≤ nat.succ (nat.add m n) : by exact nat.le_of_lt (nat.lt_succ_of_le (nat.le_of_eq rfl))
      ... = nat.add m (nat.succ n) : by { symmetry, exact add_succ_commute m n },
 },
end

lemma succ_add_nlt : ∀ m n : ℕ, ¬ nat.succ (nat.add m n) < m :=
begin
 intros m n h,
 have h' := lt_succ_add m n,
 have h'' := lt_irrfl m,
 apply h'',
 exact nat.lt_trans h' h,
end

-- again, could be tidied up
lemma succ_add_minus_is_succ : ∀ m n : ℕ, nat.succ (nat.add m n) - m = nat.succ n :=
begin
 intros m n,
 induction n with n hn,
 { have h : nat.add m 0 = m,
   { exact nat.add_zero m, },
   have h' : 1 = nat.succ (m - m),
   { rw nat.sub_self m, },
   calc
    nat.succ (nat.add m 0) - m     = nat.succ m - m : by rw h
                               ... = nat.succ (m - m) : by exact nat.succ_sub (nat.le_of_eq rfl)
                               ... = 1 : by { symmetry, exact h' },
 },
 {
   calc
    nat.succ (nat.add m (nat.succ n)) - m     
        = nat.succ (nat.succ (nat.add m n)) - m : by rw add_succ_commute
    ... = nat.succ (nat.succ (nat.add m n) - m) : by exact nat.succ_sub 
                                                     (nat.le_of_lt (lt_succ_add m n))
    ... = nat.succ (nat.succ n)                 : by rw hn,
 },
end

lemma lt_decidable : ∀ m n : ℕ, n < m ∨ ¬ n < m :=
begin
 intros m n,
 have h : n ≤ m ∨ m ≤ n,
 { exact nat.le_total, },
 { cases h,
   have h' : n = m ∨ n < m,
   { exact nat.eq_or_lt_of_le h, },
   cases h',
   { right,
     rw h',
     exact lt_irrfl m, },
   { left,
     exact h', },
 { right,
   have h' : m = n ∨ m < n,
   { exact nat.eq_or_lt_of_le h, },
   cases h',
   { rw h',
     exact lt_irrfl n, },
   { intro h'',
     apply lt_irrfl m,
     exact nat.lt_trans h' h'', },},},
end


