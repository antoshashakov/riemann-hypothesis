import Lib.Cohomology.Hodge.GrothendieckSymbol

/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Class of the diagonal in Hodge cohomology, glued from local Grothendieck symbols. -/
namespace New.Variety

open CategoryTheory MonoidalCategory Ideal Set EtaleChart

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory MonoidalCategory Ideal Set EtaleChart
attribute [-simp] Fin.natAdd_eq_addNat IsScalarTower.coe_toAlgHom'
attribute [local simp] Set.range_subset_iff Pi.single_apply sub_eq_zero
attribute [local simp] relFreeAb.map_comp_map


section OursKept

variable {k : Type} [Field k] {X : CommAlg k ⥤ Type 1} {d : ℕ}

structure IsDiagonalSymbolOn [CharZero k]
    (δ : HodgeH (relFreeAb (offDiagonal X)) d) (a : EtaleChart d X)
    (O : Subfunctor (X ⊗ X)) : Prop where
  /-- The first component of a point of `O` lies in the chart `a`. -/
  fst_mem_locus {B : CommAlg k} {p : (X ⊗ X).obj B} (hp : p ∈ O.obj B) : p.fst ∈ a.locus.obj B
  /-- The second component of a point of `O` lies in the chart `a`. -/
  snd_mem_locus {B : CommAlg k} {p : (X ⊗ X).obj B} (hp : p ∈ O.obj B) : p.snd ∈ a.locus.obj B
  /-- At a point `p` of `O` given by `φ` and `ψ` in the chart, the differences of the coordinates
  cut out the diagonal and `δ` is their symbol. -/
  isLocalSymbol {B : CommAlg k} {p : (X ⊗ X).obj B} (hp : p ∈ O.obj B) {φ ψ : a.coordRing ⟶ B}
    (hφ : X.map φ a.point = p.fst) (hψ : X.map ψ a.point = p.snd) :
    IsLocalSymbol δ p (fun (C : CommAlg k) (q : (X ⊗ X).obj C) ↦ q.fst = q.snd)
      (fun i : Fin d ↦ φ (a.coordinate i) - ψ (a.coordinate i)) 1

end OursKept

variable {k : Type} [Field k] {X : CommAlg k ⥤ Type 1} {d : ℕ}

/-- Class of the diagonal: if X has an atlas of dimension d, some δ in Hdg^d(X × X, complement
of the diagonal) is, near each diagonal field point, the symbol [df/f], where f_i = x_i ⊗ 1
− 1 ⊗ x_i for chart coordinates x cut out the diagonal.

Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). -/
private lemma exists_diagonal_class_aux [CharZero k] (hX : HasAtlas d X) :
    ∃ δ : HodgeH (relFreeAb (offDiagonal X)) d, ∀ (K : CommAlg k) (z : X.obj K), IsField K.carrier →
      ∃ (a : EtaleChart d X) (O : Subfunctor (X ⊗ X)), IsOpenSubfunctor O ∧ (z, z) ∈ O.obj K ∧
        ∀ (B : CommAlg k) (p : (X ⊗ X).obj B), p ∈ O.obj B → ∃ φ ψ : a.coordRing ⟶ B,
          X.map φ a.point = p.1 ∧ X.map ψ a.point = p.2 ∧
          IsLocalSymbol δ p (fun _ x ↦ x.1 = x.2)
            (fun i ↦ φ (a.coordinate i) - ψ (a.coordinate i)) 1 := by
  obtain ⟨_, a, ha⟩ := hX
  choose e h using exists_eq_iff_coordinate_eq ∘' a
  let V i := away (.prod ..) (e i)
  let l {i} : _ ⟶ (V i).coordRing := CommAlg.toAway _
  have Q {n W V} (e : locus (d := n) V = W) := hodge_excision (U := (offDiagonal X).preimage W.ι)
    (V.comap W.ι ⟨_, e ▸ V.point_mem_locus⟩ rfl).isOpenSubfunctor (e ▸
        by rintro _ _ ⟨_, _, ⟨⟩⟩; tauto) rfl
  choose x E using fun i ↦
    ((Q rfl d).2 _).imp (q := (IsLocalSymbol (X := (V i).locus.toFunctor) · ⟨_, point_mem_locus _⟩
    (fun _ x ↦ x.1.1 = x.1.2) _ 1)) fun _ ↦ (⟨fun C α ↦ by simpa [span_le, -map_sub] using! ((h i _
    (l ≫ α)).trans (and_iff_right ((CommAlg.exists_toAway_comp_iff ..).1 ⟨α, rfl⟩))).symm, _, ·⟩)
  have G {i B p χ} h : IsLocalSymbol (R := B) (x i) ⟨p, χ, h⟩ .. := h.rec ((E i).map _)
  have N {K} k z : ∃ i, (z, z) ∈ (V i).locus _ := (ha K k z).imp fun i m ↦
    ((range_pointMap_prod ..).ge _ ⟨m,
    m⟩).elim fun _ E ↦ E.subst ((mem_locus_away ..).2 ((h ..).1 (E ▸ mem_diagonal z :)).1)
  refine (relFreeAb.exists_glued_class _ {A | ∃ i c, (locus c).whisker _ = A ∧ c.locus ≤
    (V i).locus} (fun _ ⟨i, c, e, h⟩ _ ⟨_, b, E, _⟩ ↦ (c.exists_locus_eq_inf b).elim (⟨i, ·, · ▸
    ⟨congr($e ⊓ $E), by order⟩⟩)) (fun _ ⟨i, c, E, h⟩ m n ↦ E ▸ (h _ c.point_mem_locus).elim fun _
    e ↦ ⟨fun _ _ ↦ ((c.exists_section_isCohomEquiv.choose_spec.2 ((G
        e).1.preimage_fieldLocus_not.trans
    (by simp [EtaleChart.restrict, Pi.sub_def, away, EtaleChart.prod, ← map_sub]
        rfl))).2.comp_iff.2 (Q rfl) _).1 ((hodge_vanishing_along_diagonal (EtaleChart.restrict _ e
    c.injective c.isOpenSubfunctor).etale n).1 ..)⟩) _ (⟨·, _, rfl, le_rfl⟩)
    (hasZariskiDescent_hodgeCoeff (isZariskiLocallyTop_of_open_cover fun _ k ⟨z, _⟩ ↦ by_cases
    (· ▸ (N k z).elim (⟨_, isOpenSubfunctor <| V ·, ·, le_sup_of_le_left (le_sSup ⟨_, rfl⟩)⟩)) (⟨_,
    isOpenSubfunctor_offDiagonal, mem_offDiagonal_of_ne k ·, le_sup_right⟩))) x fun i j ↦
    ((V i).exists_locus_eq_inf (V j)).elim fun c e ↦ (e ▸ c.point_mem_locus
    :).elim fun ⟨_, m⟩ ⟨_, n⟩ ↦ ?_).imp fun δ H K z k ↦ (N k z).elim
      (⟨a ·, _, isOpenSubfunctor _, ·,
    fun | _, _, ⟨⟨χ⟩, rfl⟩ => ⟨tensorInl ≫ l ≫ χ, tensorInr ≫ l ≫ χ, ?_⟩⟩)
  simpa [← map_sub] using ⟨rfl, rfl, by peel 2 G rfl; erw [← H,
    ← δ.map_comp _ (relFreeAb.map _ le_rfl), relFreeAb.map_comp_map] at this; tauto⟩
  obtain ⟨⟨D, _, u⟩, F, _, v⟩ := G m, G n
  refine (Q e _).1 (.trans ?_ (u.trans (c.symbolClass_eq_of_cutsOutLocus D F ▸ v ▸ ?_))) <;>
    erw [← (x _).map_comp _ (relFreeAb.restrict _ (by simp)), relFreeAb.map_comp_map] <;> rfl

/-- Class of the diagonal: if X has an atlas of dimension d, some δ in Hdg^d(X × X, complement of
the diagonal) is, near each point of the diagonal, the local symbol of the differences of the
coordinates of a chart. -/
lemma exists_diagonal_class [CharZero k] (hX : HasAtlas d X) :
    ∃ δ : HodgeH (relFreeAb (offDiagonal X)) d,
      ∀ (K : CommAlg k) (z : X.obj K), IsField K.carrier →
        ∃ (a : EtaleChart d X) (O : Subfunctor (X ⊗ X)),
          IsOpenSubfunctor O ∧
          (z, z) ∈ O.obj K ∧
          IsDiagonalSymbolOn δ a O := by
  obtain ⟨δ, h⟩ := exists_diagonal_class_aux hX
  refine ⟨δ, fun K z hK ↦ ?_⟩
  obtain ⟨a, O, hO, hz, H⟩ := h K z hK
  refine ⟨a, O, hO, hz, ⟨fun {B p} hp ↦ ?_, fun {B p} hp ↦ ?_, fun {B p} hp φ' ψ' hφ hψ ↦ ?_⟩⟩
  · obtain ⟨φ, ψ, h1, -, -⟩ := H B p hp
    exact ⟨⟨φ⟩, h1⟩
  · obtain ⟨φ, ψ, -, h2, -⟩ := H B p hp
    exact ⟨⟨ψ⟩, h2⟩
  · obtain ⟨φ, ψ, h1, h2, h3⟩ := H B p hp
    obtain rfl := a.injective B (hφ.trans h1.symm)
    obtain rfl := a.injective B (hψ.trans h2.symm)
    exact h3

end New.Variety
