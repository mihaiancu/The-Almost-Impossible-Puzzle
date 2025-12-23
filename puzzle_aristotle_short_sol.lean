/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2531b001-77a2-4cd3-baeb-367ddb8fc12f

The following was proved by Aristotle:
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.StdBasis
import Init.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset

theorem puzzle (n : ℕ) (hn : 1 ≤ n) : let Z2n := (Fin n → ZMod 2)
  (∃ f:Z2n → Fin n,
    ∀ (z: Z2n) (k:Fin n),
      ∃ (i:Fin n), f (z+(Pi.single i 1))=k)
  ↔
  (∃ m:ℕ,n=2^m) := by
    constructor;
    · intro h
      obtain ⟨f, hf⟩ := h
      by_contra h_not_pow_of_two
      have h_div : n ∣ 2^n := by
        -- For each $z \in \mathbb{Z}_2^n$, the set $\{f(z + e_i) \mid i \in \{0, 1, \ldots, n-1\}\}$ must cover all of $\mathbb{Z}_n$.
        have h_cover : ∀ z : (Fin n) → (ZMod 2), Finset.image (fun i => f (z + Pi.single i 1)) Finset.univ = Finset.univ := by
            exact fun z =>  Finset.eq_univ_of_forall
                              fun k => by obtain ⟨ i, hi ⟩ := hf z k; exact Finset.mem_image.mpr ⟨ i, Finset.mem_univ _, hi ⟩ ;
        -- Consider the sum $\sum_{z \in \mathbb{Z}_2^n} \sum_{i=0}^{n-1} \delta_{f(z + e_i), k}$
        -- for each $k \in \mathbb{Z}_n$, where $\delta$ is the Kronecker delta.
        have h_sum : ∀ k : Fin n, ∑ z : (Fin n) → (ZMod 2), ∑ i : Fin n,
                                  (if f (z + Pi.single i 1) = k then 1 else 0) = 2^n := by
          intro k; rw [ Finset.sum_comm ] ; simp_all;
          rw [ ← Finset.card_biUnion ];
          · convert Finset.card_univ ( α := Fin n → ZMod 2 ) using 2 ;
            ext z; aesop; norm_num [ Fintype.card_pi ];
          · intro i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
            intro z hz₁ hz₂;
            have := Finset.card_image_iff.mp ( by
              aesop : Finset.card ( Finset.image ( fun i => f ( z + Pi.single i 1 ) ) Finset.univ ) = Finset.card Finset.univ ) ;
            simp_all +decide [ Function.Injective ] ;
            exact hij ( @this i j ( by aesop ) );
        -- On the other hand, we can rewrite the inner sum as $\sum_{i=0}^{n-1} \sum_{z \in \mathbb{Z}_2^n} \delta_{f(z + e_i), k}$.
        have h_sum_rewrite : ∀ k : Fin n, ∑ i : Fin n, ∑ z : (Fin n) → (ZMod 2),
                                          (if f (z + Pi.single i 1) = k then 1 else 0) = 2^n := by
                exact fun k => by rw [ ← h_sum k, Finset.sum_comm ] ;
        -- Since $\sum_{z \in \mathbb{Z}_2^n} \delta_{f(z + e_i), k}$ is the number of times $k$ appears in the image of $f$ over
        -- the set $\{z + e_i \mid z \in \mathbb{Z}_2^n\}$, and this set is just a shifted version of $\mathbb{Z}_2^n$,
        -- we have $\sum_{z \in \mathbb{Z}_2^n} \delta_{f(z + e_i), k} = \sum_{z \in \mathbb{Z}_2^n} \delta_{f(z), k}$.
        have h_sum_shift : ∀ i : Fin n, ∀ k : Fin n, ∑ z : (Fin n) → (ZMod 2),
                           (if f (z + Pi.single i 1) = k then 1 else 0) =
                           ∑ z : (Fin n) → (ZMod 2), (if f z = k then 1 else 0) := by
          intro i k; rw [ eq_comm ] ; rw [ ← Equiv.sum_comp ( Equiv.addRight ( Pi.single i 1 ) ) ] ; aesop;
        simp_all;
        exact dvd_of_mul_right_eq _ ( h_sum_rewrite ⟨ 0, hn ⟩ );
      rw [ Nat.dvd_prime_pow ] at h_div <;> aesop ( simp_config := { decide := true } );
    · intro h;
      obtain ⟨m, hm⟩ := h;
      -- Let's define the function $f$ for the case when $n = 2^m$.
      obtain ⟨f, hf⟩ : ∃ f : (Fin (2 ^ m) → ZMod 2) → Fin (2 ^ m),
                      ∀ z : Fin (2 ^ m) → ZMod 2, ∀ k : Fin (2 ^ m),
                      ∃ i : Fin (2 ^ m), f (z + Pi.single i 1) = k := by
        -- We can construct such a function $f$ by using the fact that $Fin (2^m)$
        -- is isomorphic to the vector space $(\mathbb{Z}/2\mathbb{Z})^m$.
        have h_iso : Nonempty (Fin (2 ^ m) ≃ (Fin m → ZMod 2)) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp [ Fintype.card_pi ] ⟩;
        obtain ⟨ e ⟩ := h_iso;
        -- Define $f$ such that $f(z) = e^{-1}(\sum_{i=0}^{m-1} z_i e(i))$.
        use fun z => e.symm (∑ i, z i • e i);
        intro z k; use e.symm ( e k - ∑ i, z i • e i ) ; simp [ Finset.sum_add_distrib, add_smul ] ;
      subst hm; exact ⟨ f, hf ⟩ ;
