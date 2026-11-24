module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import ReciprocityTheory.Hypotheses.GalCohDefs

/-!
# The Φ-condition from finiteness of `H¹`

If every continuous `ZMod n`-representation of a compact group `Γ` on a finite discrete module
has finite `H¹`, then `Γ` satisfies `PhiCond Γ n`: each open subgroup has only finitely many
continuous homomorphisms to `ZMod n`. Apply the hypothesis to the permutation representation on
`Γ ⧸ H → ZMod n` (Shapiro); a homomorphism `H → ZMod n` gives an inflated cocycle, injectively.
This argument was proved separately in six modules.
-/

@[expose] public section

open ReciprocityTheory.Gal UpperTheory.V.Alg

namespace Formalism.SharedLemmas

/-- The permutation representation of `Γ` on functions on `Γ ⧸ H`. -/
def permRepQuot (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

theorem permRepQuot_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ)
    (g : Γ) (f : Γ ⧸ H → R) (x : Γ ⧸ H) : permRepQuot R H g f x = f (g⁻¹ • x) := rfl

theorem quotOut_sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

theorem phiCond_of_finite_H1 {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (n : ℕ) [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M]
      [DiscreteTopology M] [Finite M] (ρ : Representation (ZMod n) Γ M),
      ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x =>
    continuous_inv.smul continuous_const
  have hc : ContAction (permRepQuot (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 :=
      continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permRepQuot (ZMod n) H)) := by
    have hB : Finite (B1 (permRepQuot (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permRepQuot (ZMod n) H)).comap
        (Z1 (permRepQuot (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permRepQuot (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ :=
    fun φ hφ => continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} →
      Z1 (permRepQuot (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, quotOut_sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x =>
        continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permRepQuot_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, quotOut_sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

end Formalism.SharedLemmas
