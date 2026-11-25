module

public import GroundTheory.AutomorphicForms.GL2.GJFELeviPeel
public import GroundTheory.AutomorphicForms.GL2.GJFELeviConv
public import GroundTheory.AutomorphicForms.GL2.GJFEBlock
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe
import GroundTheory.AutomorphicForms.GL2.GJInducedZeta
import GroundTheory.AutomorphicForms.LocallyProfinite
import Mathlib.Tactic.Ring

public section

noncomputable section

namespace GroundTheory.Automorphic.GodementJacquet

open Matrix GLnLocal MeasureTheory Measure Parabolic
open scoped NNReal ENNReal

universe uF uι uH w

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [∀ n : ℕ, MeasurableSpace (GL (Fin n) F)] [∀ n : ℕ, BorelSpace (GL (Fin n) F)]
  {ι : Type uι} [Fintype ι] [DecidableEq ι] {d : ι → ℕ} [∀ i, NeZero (d i)] {a : ι}
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

local notation "TailIndices" => {i : ι // i ≠ a}
local notation "Block" => GL (Fin (d a)) F
local notation "BlockMat" => Matrix (Fin (d a)) (Fin (d a)) F
set_option quotPrecheck false in
local notation "TailGroup" => (∀ j : TailIndices, GL (Fin (d j)) F)
set_option quotPrecheck false in
local notation "TestFamily" => (∀ i : ι, Matrix (Fin (d i)) (Fin (d i)) F → ℂ)
set_option quotPrecheck false in
local notation "TailTestFamily" => (∀ j : TailIndices, Matrix (Fin (d j)) (Fin (d j)) F → ℂ)

private theorem prod_splitSymm_block (f : ∀ i, GL (Fin (d i)) F → ℂ)
    (g : Block) (y : TailGroup) :
    ∏ i, f i (splitSymm d a g y i) = f a g * ∏ j : TailIndices, f j (y j) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ a, splitSymm_apply_self]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [splitSymm_apply_ne]

/-- Combine the single block and remaining blocks by expanding against a basis of the
compact-open fixed subspace. The input equations for the block use that same basis. -/
theorem block_mul_tail_FE {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {μ : ∀ i, Measure (GL (Fin (d i)) F)} [∀ i, (μ i).IsHaarMeasure]
    {ρ : Representation ℂ ((∀ i, GL (Fin (d i)) F) × H) W}
    {ρ₁ : Representation ℂ (Block × (TailGroup × H)) W}
    {ρ₂ : Representation ℂ (TailGroup × (Block × H)) W}
    (hρ₁ : ∀ g y h, ρ₁ (g, (y, h)) = ρ (splitSymm d a g y, h))
    (hρ₂ : ∀ y g h, ρ₂ (y, (g, h)) = ρ (splitSymm d a g y, h))
    (hadm₁ : IsAdmissible ρ₁) {γa γ' : RatFunc ℂ} {sa s₀ s₂ : ℝ}
    {Ψ : TestFamily} (hΨ : ∀ i, IsSchwartzBruhat (Ψ i))
    {w : W} {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual ρ))
    (hℓ₁ : ℓ ∈ smoothVectors (Representation.dual ρ₁))
    (hℓ₂ : ℓ ∈ smoothVectors (Representation.dual ρ₂))
    (hblock : ∀ Φ : BlockMat → ℂ, IsSchwartzBruhat Φ → ∀ v : W,
      ∀ ν ∈ smoothVectors (Representation.dual ρ₁),
        (∀ s : ℂ, sa < s.re → Integrable (fun g : Block =>
          Φ (g : BlockMat) * detPow g s * ν (ρ₁ (g, 1) v)) (μ a)) ∧
        (∀ s : ℂ, s.re < -sa → Integrable (fun g : Block =>
          GJMatrix.localMatrixFourier ψ Φ (g : BlockMat) * detPow g (d a - s) *
            ν (ρ₁ (g⁻¹, 1) v)) (μ a)) ∧
        RatFE F γa (blockA (μ a) ρ₁ Φ v ν)
          (blockB (μ a) ρ₁ (GJMatrix.localMatrixFourier ψ Φ) v ν))
    (hIH : ∀ Φ : TailTestFamily, (∀ i, IsSchwartzBruhat (Φ i)) →
      ∀ v : W, ∀ ν ∈ smoothVectors (Representation.dual ρ₂),
        RatFE F γ' (fun s => ∫ y, multiA ρ₂ Φ v ν s y ∂Measure.pi (fun j : TailIndices => μ j))
          (fun s => ∫ y, multiB ρ₂ (fun j => GJMatrix.localMatrixFourier ψ (Φ j)) v ν s y
            ∂Measure.pi (fun j : TailIndices => μ j)))
    (hconv : ∀ Φ : TestFamily, (∀ i, IsSchwartzBruhat (Φ i)) →
      ∀ v : W, ∀ ν ∈ smoothVectors (Representation.dual ρ),
        (∀ s : ℂ, s₀ < s.re → Integrable (multiA ρ Φ v ν s) (Measure.pi μ)) ∧
        (∀ s : ℂ, s.re < -s₀ → Integrable (multiB ρ Φ v ν s) (Measure.pi μ)))
    (hconv₂ : ∀ Φ : TailTestFamily, (∀ i, IsSchwartzBruhat (Φ i)) →
      ∀ v : W, ∀ ν ∈ smoothVectors (Representation.dual ρ₂),
        (∀ s : ℂ, s₂ < s.re → Integrable (multiA ρ₂ Φ v ν s) (Measure.pi (fun j : TailIndices => μ j))) ∧
        (∀ s : ℂ, s.re < -s₂ → Integrable (multiB ρ₂ Φ v ν s) (Measure.pi (fun j : TailIndices => μ j))))
    (hSumA : ∀ {Ka : Subgroup Block} {K' : Subgroup (TailGroup × H)},
      (hKc : IsCompact (↑(Ka.prod K') : Set (Block × (TailGroup × H)))) →
      (hKo : IsOpen (↑(Ka.prod K') : Set (Block × (TailGroup × H)))) →
      ∀ [FiniteDimensional ℂ (fixedVectors ρ₁ (Ka.prod K'))], Ka ≤ integralGL F (d a) →
      ∀ {Φ : BlockMat → ℂ}, (∀ k ∈ Ka, ∀ X, Φ ((k : BlockMat) * X) = Φ X) →
      ∀ {v : W}, v ∈ fixedVectors ρ₁ (Ka.prod K') → ∀ {s : ℂ},
      (∀ ν ∈ smoothVectors (Representation.dual ρ₁), Integrable (fun g : Block =>
        Φ (g : BlockMat) * detPow g s * ν (ρ₁ (g, 1) v)) (μ a)) →
      ∀ ν : smoothVectors (Representation.dual ρ₁),
        blockA (μ a) ρ₁ Φ v ν s = ∑ i, (ν : Module.Dual ℂ W)
          (Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K')) i : W) *
        blockA (μ a) ρ₁ Φ v (((extendFixed hadm₁.1 hKc hKo
          ((Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K'))).coord i) :
            fixedVectors (contragredient ρ₁) (Ka.prod K')) : smoothVectors
              (Representation.dual ρ₁)) : Module.Dual ℂ W) s)
    (hSumB : ∀ {Ka : Subgroup Block} {K' : Subgroup (TailGroup × H)},
      (hKc : IsCompact (↑(Ka.prod K') : Set (Block × (TailGroup × H)))) →
      (hKo : IsOpen (↑(Ka.prod K') : Set (Block × (TailGroup × H)))) →
      ∀ [FiniteDimensional ℂ (fixedVectors ρ₁ (Ka.prod K'))], Ka ≤ integralGL F (d a) →
      ∀ {Φ : BlockMat → ℂ}, (∀ k ∈ Ka, ∀ X, Φ (X * (k : BlockMat)) = Φ X) →
      ∀ {v : W}, v ∈ fixedVectors ρ₁ (Ka.prod K') → ∀ {s : ℂ},
      (∀ ν ∈ smoothVectors (Representation.dual ρ₁), Integrable (fun g : Block =>
        Φ (g : BlockMat) * detPow g (d a - s) * ν (ρ₁ (g⁻¹, 1) v)) (μ a)) →
      ∀ ν : smoothVectors (Representation.dual ρ₁),
        blockB (μ a) ρ₁ Φ v ν s = ∑ i, (ν : Module.Dual ℂ W)
          (Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K')) i : W) *
        blockB (μ a) ρ₁ Φ v (((extendFixed hadm₁.1 hKc hKo
          ((Module.finBasis ℂ (fixedVectors ρ₁ (Ka.prod K'))).coord i) :
            fixedVectors (contragredient ρ₁) (Ka.prod K')) : smoothVectors
              (Representation.dual ρ₁)) : Module.Dual ℂ W) s) :
    RatFE F (γa * γ') (fun s => ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ)
      (fun s => ∫ x, multiB ρ (fun i => GJMatrix.localMatrixFourier ψ (Ψ i)) w ℓ s x
        ∂Measure.pi μ) := by
  classical
  obtain ⟨m₀, hm₀⟩ := (hΨ a).exists_congruence_invariant
  have hw₁ : w ∈ smoothVectors ρ₁ := hadm₁.1 w
  have hnhds : (stabilizerOf ρ₁ w : Set (GL (Fin (d a)) F × ((∀ i : {i // i ≠ a},
      GL (Fin (d i)) F) × H))) ∈ nhds ((1 : GL (Fin (d a)) F),
        (1 : (∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) :=
    (mem_smoothVectors.1 hw₁).mem_nhds (one_mem (stabilizerOf ρ₁ w))
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hnhds
  obtain ⟨Ka, hKac, hKaU⟩ := exists_openSubgroup_isCompact_subset
    (Filter.inter_mem hU ((isOpen_congruenceSubgroup F (d a) m₀).mem_nhds (one_mem _)))
  obtain ⟨K', hK'c, hK'V⟩ := exists_openSubgroup_isCompact_subset hV
  set K := (Ka : Subgroup (GL (Fin (d a)) F)).prod
    (K' : Subgroup ((∀ i : {i // i ≠ a}, GL (Fin (d i)) F) × H)) with hKdef
  have hKc : IsCompact (K : Set (Block × (TailGroup × H))) := by
    rw [hKdef, Subgroup.coe_prod]
    exact hKac.prod hK'c
  have hKo : IsOpen (K : Set (Block × (TailGroup × H))) := by
    rw [hKdef, Subgroup.coe_prod]
    exact Ka.isOpen.prod K'.isOpen
  have hKa : (Ka : Subgroup (GL (Fin (d a)) F)) ≤ integralGL F (d a) := fun k hk =>
    congruenceSubgroup_le F (d a) m₀ (hKaU hk).2
  have hΨa : ∀ k ∈ (Ka : Subgroup (GL (Fin (d a)) F)), ∀ X,
      Ψ a ((k : Matrix (Fin (d a)) (Fin (d a)) F) * X) = Ψ a X := fun k hk X =>
    (hm₀ k (hKaU hk).2 X).1
  have hΦa : ∀ k ∈ (Ka : Subgroup (GL (Fin (d a)) F)), ∀ X,
      GJMatrix.localMatrixFourier ψ (Ψ a) (X * (k : Matrix (Fin (d a)) (Fin (d a)) F)) =
        GJMatrix.localMatrixFourier ψ (Ψ a) X := fun k hk X =>
    localMatrixFourier_mul_right_of_invariant (hKa hk)
      (fun x => (hm₀ k⁻¹ (inv_mem (hKaU hk).2) x).1) X
  have hwK : w ∈ fixedVectors ρ₁ K := fun k hk =>
    hUV ⟨(hKaU (Subgroup.mem_prod.1 hk).1).1, hK'V (Subgroup.mem_prod.1 hk).2⟩
  have : FiniteDimensional ℂ (fixedVectors ρ₁ K) := hadm₁.2 K hKc hKo
  set b := Module.finBasis ℂ (fixedVectors ρ₁ K) with hb
  set L : Fin (Module.finrank ℂ (fixedVectors ρ₁ K)) → Module.Dual ℂ W := fun i =>
    (((extendFixed hadm₁.1 hKc hKo (b.coord i) : fixedVectors (contragredient ρ₁) K) :
      smoothVectors (Representation.dual ρ₁)) : Module.Dual ℂ W) with hL
  have hLsm : ∀ i, L i ∈ smoothVectors (Representation.dual ρ₁) := fun i =>
    ((extendFixed hadm₁.1 hKc hKo (b.coord i) : fixedVectors (contragredient ρ₁) K) :
      smoothVectors (Representation.dual ρ₁)).2

  have hmp := measurePreserving_piSplitAt d a μ
  have hemb : MeasurableEmbedding (Equiv.piSplitAt a fun i => GL (Fin (d i)) F) :=
    (Homeomorph.piSplitAt a fun i => GL (Fin (d i)) F).toMeasurableEquiv.measurableEmbedding
  have hprod1 : ∀ (g : GL (Fin (d a)) F) (y : ∀ i : {i // i ≠ a}, GL (Fin (d i)) F) (h : H),
      ρ (splitSymm d a g y, h) = ρ₁ (1, (y, h)) * ρ₁ (g, 1) := by
    intro g y h
    rw [← map_mul, ← hρ₁]
    congr 1
    ext1 <;> simp

  have hA : ∀ s : ℂ, max sa (max s₀ s₂) < s.re →
      ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ =
        ∑ i, blockA (μ a) ρ₁ (Ψ a) w (L i) s *
          ∫ y, multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y
            ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
    intro s hs
    simp only [max_lt_iff] at hs
    obtain ⟨hsa, hs₀, hs₂⟩ := hs
    have hint := (hconv Ψ hΨ w ℓ hℓ).1 s hs₀
    set G : GL (Fin (d a)) F × (∀ j : {i // i ≠ a}, GL (Fin (d j)) F) → ℂ :=
      fun p => multiA ρ Ψ w ℓ s (splitSymm d a p.1 p.2) with hG
    have hGF : ∀ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) = multiA ρ Ψ w ℓ s x :=
      fun x => by
        rw [hG]
        dsimp only
        rw [show splitSymm d a (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).1
          (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).2 = x from
            (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm_apply_apply x]
    have hGint : Integrable G ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) := by
      rw [← hmp.integrable_comp_emb hemb]
      exact hint.congr (Filter.Eventually.of_forall fun x => (hGF x).symm)
    have hinner : ∀ y : ∀ j : {i // i ≠ a}, GL (Fin (d j)) F, ∫ g, G (g, y) ∂(μ a) =
        ∑ i, blockA (μ a) ρ₁ (Ψ a) w (L i) s *
          multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y := by
      intro y
      set μy : smoothVectors (Representation.dual ρ₁) :=
        contragredient ρ₁ ((1 : GL (Fin (d a)) F), (y, (1 : H)))⁻¹ ⟨ℓ, hℓ₁⟩ with hμy
      have hμyv : ∀ v, (μy : Module.Dual ℂ W) v = ℓ (ρ₁ ((1 : GL (Fin (d a)) F), (y, (1 : H))) v) :=
        fun v => by rw [hμy, contragredient_apply_apply, inv_inv]
      set P : ℂ := ∏ j : {i // i ≠ a}, Ψ j (y j : Matrix (Fin (d j)) (Fin (d j)) F) *
        detPow (y j) s with hP
      have hGy : ∀ g, G (g, y) = P * (Ψ a (g : Matrix (Fin (d a)) (Fin (d a)) F) * detPow g s *
          (μy : Module.Dual ℂ W) (ρ₁ (g, 1) w)) := fun g => by
        rw [hG]
        delta multiA
        dsimp only
        rw [prod_splitSymm_block (fun i x => Ψ i (x : Matrix (Fin (d i)) (Fin (d i)) F) * detPow x s) g y,
          hprod1, Module.End.mul_apply, hμyv]
        ring
      conv_lhs => arg 2; ext g; rw [hGy]
      rw [integral_const_mul]
      have hblockA := hSumA hKc hKo hKa hΨa hwK
        (fun ν hν => (hblock (Ψ a) (hΨ a) w ν hν).1 s hsa) μy
      rw [show ∫ g, Ψ a (g : Matrix (Fin (d a)) (Fin (d a)) F) * detPow g s *
          (μy : Module.Dual ℂ W) (ρ₁ (g, 1) w) ∂(μ a) = blockA (μ a) ρ₁ (Ψ a) w μy s from rfl,
        hblockA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hμyv]
      delta multiA
      rw [show ρ₁ ((1 : GL (Fin (d a)) F), (y, (1 : H))) = ρ₂ (y, ((1 : GL (Fin (d a)) F), (1 : H))) by
        rw [hρ₁, hρ₂]]
      change P * (ℓ (ρ₂ (y, ((1 : GL (Fin (d a)) F), (1 : H))) (b i : W)) *
        blockA (μ a) ρ₁ (Ψ a) w (L i) s) = _
      rw [hP, show ((1 : GL (Fin (d a)) F), (1 : H)) = (1 : GL (Fin (d a)) F × H) from rfl]
      ring
    calc ∫ x, multiA ρ Ψ w ℓ s x ∂Measure.pi μ
        = ∫ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) ∂Measure.pi μ := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hGF x).symm)
      _ = ∫ p, G p ∂((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) :=
          hmp.integral_comp hemb G
      _ = ∫ y, ∫ g, G (g, y) ∂(μ a) ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_prod_symm G hGint
      _ = ∫ y, ∑ i, blockA (μ a) ρ₁ (Ψ a) w (L i) s *
            multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y
            ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = _ := by
          rw [integral_finsetSum _ fun i _ =>
            ((hconv₂ (fun j : {i // i ≠ a} => Ψ j) (fun j => hΨ j) (b i : W) ℓ hℓ₂).1 s
              hs₂).const_mul _]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]

  set Ψh : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F → ℂ :=
    fun i => GJMatrix.localMatrixFourier ψ (Ψ i) with hΨhdef
  have hΨh : ∀ i, IsSchwartzBruhat (Ψh i) := fun i => (hΨ i).localMatrixFourier hψ hψ1
  have hB : ∀ s : ℂ, s.re < -max sa (max s₀ s₂) →
      ∫ x, multiB ρ Ψh w ℓ s x ∂Measure.pi μ =
        ∑ i, blockB (μ a) ρ₁ (Ψh a) w (L i) s *
          ∫ y, multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y
            ∂Measure.pi (fun j : {i // i ≠ a} => μ j) := by
    intro s hs
    have hsa : s.re < -sa := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
    have hs₀ : s.re < -s₀ :=
      lt_of_lt_of_le hs (neg_le_neg ((le_max_left _ _).trans (le_max_right _ _)))
    have hs₂ : s.re < -s₂ :=
      lt_of_lt_of_le hs (neg_le_neg ((le_max_right _ _).trans (le_max_right _ _)))
    have hint := (hconv Ψh hΨh w ℓ hℓ).2 s hs₀
    set G : GL (Fin (d a)) F × (∀ j : {i // i ≠ a}, GL (Fin (d j)) F) → ℂ :=
      fun p => multiB ρ Ψh w ℓ s (splitSymm d a p.1 p.2) with hG
    have hGF : ∀ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) = multiB ρ Ψh w ℓ s x :=
      fun x => by
        rw [hG]
        dsimp only
        rw [show splitSymm d a (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).1
          (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x).2 = x from
            (Equiv.piSplitAt a fun i => GL (Fin (d i)) F).symm_apply_apply x]
    have hGint : Integrable G ((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) := by
      rw [← hmp.integrable_comp_emb hemb]
      exact hint.congr (Filter.Eventually.of_forall fun x => (hGF x).symm)
    have hinner : ∀ y : ∀ j : {i // i ≠ a}, GL (Fin (d j)) F, ∫ g, G (g, y) ∂(μ a) =
        ∑ i, blockB (μ a) ρ₁ (Ψh a) w (L i) s *
          multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y := by
      intro y
      set μy : smoothVectors (Representation.dual ρ₁) :=
        contragredient ρ₁ ((1 : GL (Fin (d a)) F), (y⁻¹, (1 : H)))⁻¹ ⟨ℓ, hℓ₁⟩ with hμy
      have hμyv : ∀ v, (μy : Module.Dual ℂ W) v =
          ℓ (ρ₁ ((1 : GL (Fin (d a)) F), (y⁻¹, (1 : H))) v) :=
        fun v => by rw [hμy, contragredient_apply_apply, inv_inv]
      set P : ℂ := ∏ j : {i // i ≠ a}, Ψh j (y j : Matrix (Fin (d j)) (Fin (d j)) F) *
        detPow (y j) ((d j : ℂ) - s) with hP
      have hGy : ∀ g, G (g, y) = P * (Ψh a (g : Matrix (Fin (d a)) (Fin (d a)) F) *
          detPow g ((d a : ℂ) - s) * (μy : Module.Dual ℂ W) (ρ₁ (g⁻¹, 1) w)) := fun g => by
        rw [hG]
        delta multiB
        dsimp only
        rw [prod_splitSymm_block (fun i x => Ψh i (x : Matrix (Fin (d i)) (Fin (d i)) F) *
            detPow x ((d i : ℂ) - s)) g y, splitSymm_inv, hprod1, Module.End.mul_apply, hμyv]
        ring
      conv_lhs => arg 2; ext g; rw [hGy]
      rw [integral_const_mul]
      have hblockB := hSumB hKc hKo hKa hΦa hwK
        (fun ν hν => (hblock (Ψ a) (hΨ a) w ν hν).2.1 s hsa) μy
      rw [show ∫ g, Ψh a (g : Matrix (Fin (d a)) (Fin (d a)) F) * detPow g ((d a : ℂ) - s) *
          (μy : Module.Dual ℂ W) (ρ₁ (g⁻¹, 1) w) ∂(μ a) = blockB (μ a) ρ₁ (Ψh a) w μy s from rfl,
        hblockB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hμyv]
      delta multiB
      rw [show ρ₁ ((1 : GL (Fin (d a)) F), (y⁻¹, (1 : H))) =
          ρ₂ (y⁻¹, ((1 : GL (Fin (d a)) F), (1 : H))) by rw [hρ₁, hρ₂]]
      change P * (ℓ (ρ₂ (y⁻¹, ((1 : GL (Fin (d a)) F), (1 : H))) (b i : W)) *
        blockB (μ a) ρ₁ (Ψh a) w (L i) s) = _
      rw [hP, show ((1 : GL (Fin (d a)) F), (1 : H)) = (1 : GL (Fin (d a)) F × H) from rfl]
      ring
    calc ∫ x, multiB ρ Ψh w ℓ s x ∂Measure.pi μ
        = ∫ x, G (Equiv.piSplitAt a (fun i => GL (Fin (d i)) F) x) ∂Measure.pi μ := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hGF x).symm)
      _ = ∫ p, G p ∂((μ a).prod (Measure.pi fun j : {i // i ≠ a} => μ j)) :=
          hmp.integral_comp hemb G
      _ = ∫ y, ∫ g, G (g, y) ∂(μ a) ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_prod_symm G hGint
      _ = ∫ y, ∑ i, blockB (μ a) ρ₁ (Ψh a) w (L i) s *
            multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y
            ∂(Measure.pi fun j : {i // i ≠ a} => μ j) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = _ := by
          rw [integral_finsetSum _ fun i _ =>
            ((hconv₂ (fun j : {i // i ≠ a} => Ψh j) (fun j => hΨh j) (b i : W) ℓ hℓ₂).2 s
              hs₂).const_mul _]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]

  have hterm : ∀ i, RatFE F (γa * γ')
      (fun s => blockA (μ a) ρ₁ (Ψ a) w (L i) s *
        ∫ y, multiA ρ₂ (fun j : {i // i ≠ a} => Ψ j) (b i : W) ℓ s y
          ∂Measure.pi (fun j : {i // i ≠ a} => μ j))
      (fun s => blockB (μ a) ρ₁ (Ψh a) w (L i) s *
        ∫ y, multiB ρ₂ (fun j : {i // i ≠ a} => Ψh j) (b i : W) ℓ s y
          ∂Measure.pi (fun j : {i // i ≠ a} => μ j)) := fun i =>
    ((hblock (Ψ a) (hΨ a) w (L i) (hLsm i)).2.2).mul
      (hIH (fun j => Ψ j) (fun j => hΨ j) (b i : W) ℓ hℓ₂)
  exact (RatFE.sum Finset.univ fun i _ => hterm i).congr ⟨_, hA⟩ ⟨_, hB⟩

end GroundTheory.Automorphic.GodementJacquet
