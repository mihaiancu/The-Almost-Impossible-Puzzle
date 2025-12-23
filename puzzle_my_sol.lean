import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.StdBasis
import Init.Data.Fin.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Fintype.Card


open Pointwise Finset Set

abbrev Z2 (n : ℕ) := Finset (Fin n → ZMod 2)

def basis (n : ℕ) : Z2 n :=
  univ.image (fun i : Fin n => Pi.single i 1)

lemma basis_card (n : ℕ) : (basis n).card = n := by
  unfold basis
  have H : Function.Injective (fun i : Fin n => Pi.single i (1:ZMod 2)) := by
     intro i j hij
     dsimp at hij
     have h := congrArg (fun f => f i) hij
     simp [Pi.single_apply] at h
     exact h
  simp [Finset.card_image_of_injective (s := univ) H]


theorem thm1 (n : ℕ) (hn : 1 ≤ n) : let Z2n := (Fin n → ZMod 2)
  (∃ f:Z2n → Fin n,
    ∀ (z: Z2n) (k:Fin n),
      ∃ (i:Fin n), f (z+(Pi.single i 1))=k)
  ↔
  (∃ m:ℕ,n=2^m)  where
mp :=by
  intro ⟨f,hf⟩
  let Z2n : Z2 n := univ
  let f_0 : Z2 n := univ.filter (fun z => f z = ⟨0, by omega⟩)
  let sum_fun := ((fun b ↦ image (fun a ↦ a + b) (basis n)) '' f_0)
  have lemma1 : sum_fun.PairwiseDisjoint id := by
    rw [PairwiseDisjoint,Set.Pairwise]
    intro Bx hBx By hBy h12 C hC1
    unfold sum_fun at hBx hBy
    rcases hBx with ⟨x, hx, hBx⟩
    dsimp at hBx
    rcases hBy with ⟨y, hy, hBy⟩
    dsimp at hBx hBy hC1 ⊢
    have ha : f x = ⟨0, by omega⟩ ∧ f y = ⟨0, by omega⟩ := by
      simp [f_0] at hx hy
      exact ⟨hx, hy⟩
    intro hC2
    refine subset_empty.mpr ?_
    refine eq_empty_of_forall_notMem ?_
    intro z hz
    have hz : z ∈ Bx ∧ z ∈ By := by
      exact ⟨hC1 hz, hC2 hz⟩
    rw [← hBx, ← hBy] at hz
    rcases hz with ⟨hBx, hBy⟩
    rw [Finset.mem_image] at hBx hBy
    rcases hBx with ⟨ei, hei, heix⟩
    rcases hBy with ⟨ej, hej, hejy⟩
    dsimp [basis] at hei hej
    rw [Finset.mem_image] at hei hej
    rcases hei with ⟨i, _, hei⟩
    rcases hej with ⟨j, _, hej⟩
    have heiz : ei + z = x := by
        calc ei + z
          _ = ei + (ei + x) := by rw [heix]
          _ = (ei + ei) + x   := by rw [add_assoc]
          _ = (Pi.single i 1 + Pi.single i 1) + x   := by simp [hei]
          _ = x   := by simp [ZModModule.add_self (Pi.single i 1)]
    have hejz : ej + z = y := by
        calc ej + z
          _ = ej + (ej + y) := by rw [hejy]
          _ = (ej + ej) + y   := by rw [add_assoc]
          _ = (Pi.single j 1 + Pi.single j 1) + y   := by simp [hej]
          _ = y   := by simp [ZModModule.add_self (Pi.single j 1)]
    have hfz_not_surj : f (z + ei) = f (z + ej) := by
      rw [add_comm z]
      nth_rewrite 2 [add_comm]
      simp [heiz, hejz, ha]
    let fz := fun k => f (z + (Pi.single k 1))
    have hfz : fz.Surjective := by
      intro l
      rcases hf z l with ⟨k, hk⟩
      use k
    have hfz : fz.Bijective := by
      apply Function.Surjective.bijective_of_finite hfz
    have hfz : fz.Injective := by
      exact Function.Bijective.injective hfz
    unfold Function.Injective at hfz
    have : fz i = fz j := by
      unfold fz
      simp [hei,hej]
      assumption
    have hfz : i = j := by
      apply hfz
      assumption
    have hfz : ei = ej := by
      rw [← hei,← hej]
      simp [hfz]
    have hfz : x = y := by
      rw [← heiz,← hejz]
      simp [hfz]
    have : Bx = By := by
      rw [← hBx, ← hBy]
      simp [hfz]
    exact h12 this
  have lemma1 := card_dvd_card_add_left lemma1
  let basis_plus_f_0 : Z2 n := (basis n) + f_0
  have lemma2 : (basis n).card ∣ basis_plus_f_0.card := by
    simp [basis_plus_f_0,lemma1]
  rw [basis_card n] at lemma2
  have lemma3 : basis_plus_f_0 = Z2n := by
    simp [basis_plus_f_0]
    ext z
    constructor
    · intro
      exact mem_univ z
    · intro hx
      unfold Z2n at hx
      have h := hf z ⟨0,by omega⟩
      rcases h with ⟨i, hi⟩
      let x := z + (Pi.single i 1)
      have hx : x ∈ f_0 := by
        simp [f_0]
        rw [hi]
      have hxi : z = x + (Pi.single i 1) := by
        simp [x,add_assoc]
        exact ZModModule.add_self (Pi.single i 1)
      rw [add_comm]
      have bi: Pi.single i 1 ∈ basis n := by
        simp [basis]
      simp [hxi]
      exact Finset.add_mem_add hx bi
  have lemma4 : Z2n.card = 2 ^ n := by
    simp [Z2n]
  have final : n ∣ 2 ^ n := by
    simp [lemma4, lemma3] at lemma2
    exact lemma2
  rw [Nat.dvd_prime_pow Nat.prime_two]  at final
  rcases final with ⟨m, hm⟩
  use m
  exact hm.2
mpr := by
  intro ⟨m, hm⟩
  subst hm
  have phi: Fin (2 ^ m) ≃ (Fin m → ZMod 2) :=
      Fintype.equivOfCardEq (by simp [Fintype.card_fin])
  use fun z : (Fin (2 ^ m) → ZMod 2) => phi.symm (∑ i, z i • phi i)
  intro z k
  use phi.symm (phi k - ∑ j, ((z j) • (phi j)))
  simp [Finset.sum_add_distrib, add_smul]
