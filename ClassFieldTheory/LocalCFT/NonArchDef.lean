import Mathlib

/-!
# Definition of Non-Archimedean Local Fields

We define non-archimedean local fields as a class `IsNonArchLF`.

-/

universe u v

class IsNonarchLocalField (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] : Prop extends
  ValuativeTopology K,
  IsUniformAddGroup K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K,
  IsTopologicalDivisionRing K, -- TODO: remove IsTopologicalDivisionRing
  ValuativeRel.IsRankLeOne K -- TODO: in future mathlib
  -- CompleteSpace K,
  -- ValuativeRel.IsDiscrete K


open ValuativeRel

namespace IsNonarchLocalField

variable (p : ℕ) [Fact p.Prime]

instance : LocallyCompactSpace ℚ_[p] := inferInstance

instance : IsNonarchLocalField ℚ_[p] where
  mem_nhds_iff := sorry
  nonempty := sorry

variable (K : Type u) [Field K] [ValuativeRel K] [UniformSpace K] [IsNonarchLocalField K]
  (L : Type v) [Field L] [ValuativeRel L] [UniformSpace L] [IsNonarchLocalField L]

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

noncomputable
instance : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne where
  hom := IsRankLeOne.nonempty.some.emb
  strictMono' := IsRankLeOne.nonempty.some.strictMono

open scoped Valued in
instance : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

instance : IsDiscreteValuationRing 𝒪[K] :=
  (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp inferInstance).2.1

instance : (Valued.v : Valuation K (ValueGroupWithZero K)).IsNontrivial :=
  ValuativeRel.isNontrivial_iff_isNontrivial.mp inferInstance

noncomputable
instance : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne where
  hom := IsRankLeOne.nonempty.some.emb
  strictMono' := IsRankLeOne.nonempty.some.strictMono

open scoped Valued in
instance : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K

open Valued.integer in
instance compactSpace_integer : CompactSpace 𝒪[K] :=
  properSpace_iff_compactSpace_integer.mp inferInstance

open Valued.integer in
instance : CompleteSpace 𝒪[K] :=
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (compactSpace_integer K)).1

open Valued.integer in
instance : Finite 𝓀[K] :=
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).2.2

theorem prime_ringChar : (ringChar 𝓀[K]).Prime :=
  CharP.char_is_prime 𝓀[K] _

open Valued.integer in
instance : CompleteSpace K :=
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

/-- This is how you show that there is a uniformiser (which in Mathlib is called `Irreducible`). -/
example : ∃ ϖ : 𝒪[K], Irreducible ϖ :=
  IsDiscreteValuationRing.exists_irreducible _

example : ∀ ϖ : 𝒪[K], Irreducible ϖ → ϖ ≠ 0 :=
  fun _ h ↦ h.ne_zero

lemma associated_iff_of_irreducible (x y : 𝒪[K]) (hx : Irreducible x) :
    Associated y x ↔ Irreducible y :=
  ⟨fun hyx ↦ hyx.symm.irreducible hx,
  fun hy ↦ IsDiscreteValuationRing.associated_of_irreducible _ hy hx⟩

theorem compact_OK : IsCompact (𝒪[K] : Set K) :=
  sorry

theorem open_OK : IsOpen (𝒪[K] : Set K) :=
  sorry

def compactOpenOK : TopologicalSpace.CompactOpens K where
  carrier := 𝒪[K]
  isCompact' := compact_OK K
  isOpen' := open_OK K

-- TODO: add Haar measure (or check that it works with `example`)

-- class HasExtension [Algebra K L] : Prop extends
--   Valuation.HasExtension (Valued.v (R := K)) (Valued.v (R := L))
class HasExtension [Algebra K L] : Prop extends ValuativeExtension K L

variable [Algebra K L] [HasExtension K L]

instance : FiniteDimensional K L :=
  sorry

open Valuation.HasExtension in
instance : Algebra 𝒪[K] 𝒪[L] where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : L) ▸ mul_mem sorry a.2⟩
  algebraMap := (algebraMap K L).restrict 𝒪[K] 𝒪[L]
    sorry
    -- (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)
  -- Valuation.HasExtension.instAlgebraInteger (R := K) (A := L) (vR := Valued.v) (vA := Valued.v)

instance : ContinuousSMul K L :=
  sorry
-- TODO: Maddy

instance : Module.Finite 𝒪[K] 𝒪[L] :=
  sorry

@[fun_prop] lemma continuous_algebraMap : Continuous (algebraMap K L) :=
  _root_.continuous_algebraMap K L

instance : IsScalarTower 𝒪[K] K L := inferInstance

instance : IsScalarTower 𝒪[K] 𝒪[L] L := sorry --inferInstance

noncomputable def e : ℕ :=
  Ideal.ramificationIdx (algebraMap 𝒪[K] 𝒪[L]) 𝓂[K] 𝓂[L]

theorem e_spec {ϖK : 𝒪[K]} {ϖL : 𝒪[L]} (hk : Irreducible ϖK) (hl : Irreducible ϖL) :
    Associated (ϖL ^ e K L) (algebraMap 𝒪[K] 𝒪[L] (ϖK)) :=
  sorry

noncomputable def f : ℕ :=
  Ideal.inertiaDeg 𝓂[K] 𝓂[L]

theorem f_spec : Nat.card 𝓀[K] ^ f K L = Nat.card 𝓀[K] :=
  sorry

theorem e_pos : 0 < e K L :=
  sorry

theorem f_pos : 0 < f K L :=
  sorry

theorem e_mul_f_eq_n : e K L * f K L = Module.finrank K L :=
  sorry

-- TODO: generalise to extensions of DVRs.
class IsUnramified : Prop where
  e_eq_one : e K L = 1

theorem unramified_def : IsUnramified K L ↔ e K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

theorem unramified_iff_unramified : IsUnramified K L ↔ Algebra.Unramified 𝒪[K] 𝒪[L] :=
  sorry

section make_finite_extension

/- # Constructing a finite extension from a minimal set of assumptions. -/

variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

open scoped Valued in
#check (inferInstance : NormedField K)
#check (inferInstance : Valuation.RankOne (Valued.v (R := K)))

@[ext] theorem _root_.ValuativeRel.ext {R : Type u} [CommRing R] {v v' : ValuativeRel R}
    (h : ∀ a b, v.rel a b ↔ v'.rel a b) : v = v' := by
  cases v; cases v'; congr; ext; apply h

theorem _root_.ValuativeRel.rel_iff_one_le {F : Type u} [Field F] [ValuativeRel F]
    {x : F} (y : F) (hx : x ≠ 0) : x ≤ᵥ y ↔ 1 ≤ᵥ x⁻¹ * y :=
  ⟨fun h ↦ by simpa [hx] using rel_mul_left x⁻¹ h,
  fun h ↦ by simpa [hx] using rel_mul_left x h⟩

@[ext high] theorem _root_.ValuativeRel.ext_field {F : Type u} [Field F] {v v' : ValuativeRel F}
    (h : ∀ x, v.rel 1 x ↔ v'.rel 1 x) : v = v' := by
  ext x y
  by_cases hx : x = 0
  · rw [hx]; simp only [ValuativeRel.zero_rel]
  rw [rel_iff_one_le y hx, @rel_iff_one_le _ _ v _ y hx]
  apply h

open scoped Valued in
include K in
theorem unique_hasExtension : ∃! v : ValuativeRel L, ValuativeExtension K L := by
  letI : NormedField L := spectralNorm.normedField K L
  haveI : IsUltrametricDist L := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_nnnorm
    isNonarchimedean_spectralNorm
  let v := NormedField.valuation (K := L)
  letI := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  refine ⟨inferInstance, ⟨fun k₁ k₂ ↦ ?_⟩, ?_⟩
  · rw [Valuation.Compatible.rel_iff_le (v := v),
      Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation K)]
    change spectralNorm K L _ ≤ spectralNorm K L _ ↔ _
    rw [spectralNorm_extends, spectralNorm_extends]
    change Valued.norm _ ≤ Valued.norm _ ↔ _
    rw [Valued.norm_def, Valued.norm_def, NNReal.coe_le_coe,
      (Valuation.RankOne.strictMono Valued.v).le_iff_le]
    rfl
  · intro v' h
    let f : AlgebraNorm K L := sorry
    -- { toFun := _ }
    ext x
    change _ ≤ᵥ _ ↔ spectralNorm K L 1 ≤ spectralAlgNorm K L x
    rw [spectralNorm_one]
    sorry

-- def of_finite_extension [ValuativeRel L] [ValuativeExtension K L] :
--     IsNonarchLocalField L :=
--   sorry
/-
failed to synthesize
  UniformSpace L
-/

end make_finite_extension

end IsNonarchLocalField
