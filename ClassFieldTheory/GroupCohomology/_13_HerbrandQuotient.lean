import Mathlib
import ClassFieldTheory.GroupCohomology._9_CyclicGroup
import ClassFieldTheory.GroupCohomology._4_TateCohomology_def
import ClassFieldTheory.Mathlib.ModuleCatExact

noncomputable section

variable {R G : Type} [CommRing R] [Group G] [Finite G] [DecidableEq G] [IsCyclic G]
variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

open CategoryTheory
  groupCohomology
  Rep
  LinearMap

namespace Representation

abbrev oneSubGen : A →ₗ[R] A := 1 - ρ (gen G)
abbrev herbrandZ0 := ker ρ.oneSubGen
abbrev herbrandZ1 := ker ρ.norm
abbrev herbrandB0 := range ρ.norm
abbrev herbrandB1 := range ρ.oneSubGen

lemma herbrandB0_le_herbrandZ0 : ρ.herbrandB0 ≤ ρ.herbrandZ0 := by
  intro _ hx
  let ⟨y, hy⟩ := hx
  rw [mem_ker, ← hy]

  apply sub_eq_zero_of_eq
  conv_lhs => rw [← norm_comm ρ (gen G)]
  simp

lemma herbrandB1_le_herbrandZ1 : ρ.herbrandB1 ≤ ρ.herbrandZ1 := by
  intro x hx
  let ⟨y, hy⟩ := hx
  rw [mem_ker, ← hy]

  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  apply sub_eq_zero_of_eq
  conv_lhs => rw [← norm_comm' ρ (gen G)]
  simp

abbrev herbrandH0 := ρ.herbrandZ0 ⧸ (ρ.herbrandB0.submoduleOf ρ.herbrandZ0)

abbrev herbrandH1 := ρ.herbrandZ1 ⧸ (ρ.herbrandB1.submoduleOf ρ.herbrandZ1)

def herbrandQuotient : ℚ := Nat.card ρ.herbrandH0 / Nat.card ρ.herbrandH1

@[to_additive cardFKerTimesCardFRangeEqCardGAdd]
lemma cardFKerTimesCardFRangeEqCardGMul {G H:Type } [Group G] [Group H] [Finite G] ( f : G →*  H): Nat.card f.ker * Nat.card f.range = Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker]
  suffices Nat.card f.range = Nat.card (G ⧸ f.ker) by
    rw [← this]
    ring_nf
  apply Eq.symm
  apply Nat.card_eq_of_bijective _  (MulEquiv.bijective (QuotientGroup.quotientKerEquivRange f))

lemma eqMulOfMulEq (a b c d : Nat) (hab : a = b) (hcd : c = d) : a*c =b*d  := by
  grinds

lemma herbrandQuotient_of_finite [Finite A] : ρ.herbrandQuotient = 1 := by
  /-
  Consider the linear maps `f₁ f₂ : M → M` defined to be multiplication by `1 - gen G`
  and norm respectively. The kernel of `f₁` is the submodule of `G`-invariants, and the
  cokernel of `f₁` is the quotient module of coinvariants. We therefore have (for Tate groups):

    `H⁰(G,M) ≅ ker f₁ ⧸ range f₂` and `H⁻¹(G,M) ≅ ker f₂ ⧸ range f₁`.

  The result follows because `|ker fᵢ| * |range fᵢ| = |M|` for `i=1,2`.
  -/
  unfold herbrandQuotient
  apply (div_eq_one_iff_eq _ ).2
  apply congrArg Nat.cast

  have cardH0 : Nat.card ρ.herbrandB0 * Nat.card ρ.herbrandH0 = Nat.card ρ.herbrandZ0 := by
    rw [Submodule.card_eq_card_quotient_mul_card (ρ.herbrandB0.submoduleOf ρ.herbrandZ0)]
    apply eqMulOfMulEq
    · apply Nat.card_congr
      exact(Submodule.submoduleOfEquivOfLe (herbrandB0_le_herbrandZ0 ρ)).symm.toEquiv
    · rfl

  have cardH1 : Nat.card ρ.herbrandB1 * Nat.card ρ.herbrandH1 = Nat.card ρ.herbrandZ1 := by
    rw [Submodule.card_eq_card_quotient_mul_card (ρ.herbrandB1.submoduleOf ρ.herbrandZ1)]
    apply eqMulOfMulEq
    · apply Nat.card_congr
      exact (Submodule.submoduleOfEquivOfLe (herbrandB1_le_herbrandZ1 ρ)).symm.toEquiv
    · rfl

  have rankTheorem1 : (Nat.card ρ.herbrandZ1) * Nat.card ρ.herbrandB0 = Nat.card A := by exact cardFKerTimesCardFRangeEqCardGAdd (ρ.norm.toAddMonoidHom)
  have rankTheorem2 : (Nat.card ρ.herbrandZ0) * Nat.card ρ.herbrandB1 = Nat.card A := by exact cardFKerTimesCardFRangeEqCardGAdd (ρ.oneSubGen.toAddMonoidHom)

  suffices (Nat.card ρ.herbrandB1) * (Nat.card ρ.herbrandB0) * Nat.card ρ.herbrandH0 = (Nat.card ρ.herbrandB1) * (Nat.card ρ.herbrandB0) * Nat.card ρ.herbrandH1 by
    simp only [mul_eq_mul_left_iff] at this

    cases this
    · assumption
    · exfalso
      have : (Nat.card ρ.herbrandB1) * (Nat.card ρ.herbrandB0) > 0 := by
        apply Nat.mul_pos Nat.card_pos Nat.card_pos
      linarith

  calc (Nat.card ρ.herbrandB1) * (Nat.card ρ.herbrandB0) * (Nat.card ρ.herbrandH0) = Nat.card A := by rw [mul_assoc, mul_comm, cardH0, ← rankTheorem2]

    _ = (Nat.card ρ.herbrandB1) * (Nat.card ρ.herbrandB0) * (Nat.card ρ.herbrandH1) := by rw [mul_assoc, mul_comm, mul_assoc, mul_comm (Nat.card ρ.herbrandH1), cardH1, ← rankTheorem1, mul_comm]

  apply Nat.cast_ne_zero.mpr
  apply Nat.card_ne_zero.mpr
  exact ⟨Nonempty.intro 0, Quotient.finite (ρ.herbrandB1.submoduleOf ρ.herbrandZ1).quotientRel⟩

end Representation

namespace Rep

def herbrandQuotient (M : Rep R G) : ℚ :=
    Nat.card (groupCohomology M 2) / Nat.card (groupCohomology M 1)

lemma herbrandQuotient_of : herbrandQuotient (of ρ) = ρ.herbrandQuotient :=
  /-
  show that `herbrandH0` and `herbrandH1` are isomorphic to the Tate cohomology groups
  `H⁰` and `H¹`. Then use the periodicity of the Tate cohomology groups.
  -/
  sorry

lemma herbrandQuotient_of_finite (M : Rep R G) [Finite M] : M.herbrandQuotient = 1 :=
  /-
  This is proved above for `Representation`.
  -/
  sorry

section six_term_sequence
variable {S : ShortComplex (Rep R G)} (hS : S.ShortExact)

def herbrandSixTermSequence : CochainComplex (ModuleCat R) (Fin 6) where
  X
  | 0 => groupCohomology S.X₁ 2
  | 1 => groupCohomology S.X₂ 2
  | 2 => groupCohomology S.X₃ 2
  | 3 => groupCohomology S.X₁ 1
  | 4 => groupCohomology S.X₂ 1
  | 5 => groupCohomology S.X₃ 1
  d
  | 0,1 => (functor R G 2).map S.f
  | 1,2 => (functor R G 2).map S.g
  | 2,3 => δ hS 2 3 rfl ≫ (periodicCohomology 0).inv.app S.X₁
  | 3,4 => (functor R G 1).map S.f
  | 4,5 => (functor R G 1).map S.g
  | 5,0 => δ hS 1 2 rfl
  | _,_ => 0
  shape i j _ := by fin_cases i,j <;> tauto
  d_comp_d' i _ _ hij hjk := by
    simp only [ComplexShape.up', ComplexShape.up, Fin.isValue] at hij hjk
    rw [←hjk, ←hij]
    fin_cases i
    all_goals
      dsimp
      try simp_rw [← groupCohomology.map_comp]
    ·
      sorry
    ·
      sorry
    ·
      sorry
    all_goals sorry

lemma herbrandSixTermSequence_exactAt (i : Fin 6) : (herbrandSixTermSequence hS).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  fin_cases i
  all_goals
    simp
    apply ShortComplex.Exact.moduleCat_of_ker_le_range
    intro w hw_ker
    simp
  ·




  /-
  It should be possible to get this out of Mathlib.
  -/
  all_goals sorry

lemma herbrandQuotient_nonzero_of_shortExact₃
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0) :
    S.X₃.herbrandQuotient ≠ 0 := by
  sorry

lemma herbrandQuotient_nonzero_of_shortExact₂
  (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
  S.X₂.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_nonzero_of_shortExact₁
  (h₁ : S.X₂.herbrandQuotient ≠ 0) (h₃ : S.X₃.herbrandQuotient ≠ 0) :
  S.X₁.herbrandQuotient ≠ 0 := sorry

lemma herbrandQuotient_eq_of_shortExact
    (h₁ : S.X₁.herbrandQuotient ≠ 0) (h₂ : S.X₂.herbrandQuotient ≠ 0)
    (h₃ : S.X₃.herbrandQuotient ≠ 0) :
    S.X₂.herbrandQuotient = S.X₁.herbrandQuotient * S.X₃.herbrandQuotient :=
  /-
  We have a six term long exact sequence of finite `R`-modules.
  Hence the products of the orders of the even terms is
  equal to the product of the orders of the odd terms.
  This implies the relation.
  -/
  sorry

end six_term_sequence

end Rep
