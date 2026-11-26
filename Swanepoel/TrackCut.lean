module
public import Swanepoel.TrackSimplicity
public import Swanepoel.RhombusTransitions
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PositiveSpineCutStep {n : ℕ} {G : PennyGraph n} (e f a b : OrientedEdge G) : Prop :=
  PositiveCellStep a b ∧ ¬(a=e ∧ b=f)

abbrev SpineCutComponent {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) :=
  Quotient (Relation.EqvGen.setoid (PositiveSpineCutStep e f))

def spineCutComponent {n : ℕ} {G : PennyGraph n} (e f a : OrientedEdge G) :
    SpineCutComponent e f := Quotient.mk _ a

theorem cut_step_predecessor_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f a b : OrientedEdge G} (hef : PositiveCellStep e f)
    (hab : PositiveSpineCutStep e f a b) :
    Relation.ReflTransGen PositiveCellStep a e ↔ Relation.ReflTransGen PositiveCellStep b e := by
  constructor
  · intro hae
    rcases hae.cases_head with h | ⟨g,hag,hge⟩
    · subst a
      have hh := positive_step_functional ht hab.1 hef
      exact False.elim (hab.2 ⟨rfl,hh⟩)
    · have hh := positive_step_functional ht hab.1 hag
      simpa only [hh] using hge
  · intro hbe
    exact (Relation.ReflTransGen.single hab.1).trans hbe

theorem cut_component_predecessor_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f a b : OrientedEdge G} (hef : PositiveCellStep e f)
    (hab : Relation.EqvGen (PositiveSpineCutStep e f) a b) :
    Relation.ReflTransGen PositiveCellStep a e ↔ Relation.ReflTransGen PositiveCellStep b e := by
  induction hab with
  | rel _ _ h => exact cut_step_predecessor_iff ht hef h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem cut_step_endpoints_disconnected {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (hef : PositiveCellStep e f) :
    spineCutComponent e f e≠spineCutComponent e f f := by
  intro h
  have hfe := (cut_component_predecessor_iff ht hef (Quotient.exact h)).mp
    Relation.ReflTransGen.refl
  exact no_closed_positive_spine e (Relation.TransGen.head' hef hfe)

theorem path_before_cut_survives {n : ℕ} {G : PennyGraph n}
    {e f a : OrientedEdge G} (hef : PositiveCellStep e f)
    (hae : Relation.ReflTransGen PositiveCellStep a e) :
    Relation.ReflTransGen (PositiveSpineCutStep e f) a e := by
  induction hae using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hbe ih =>
    apply ih.head
    refine ⟨hab,?_⟩
    rintro ⟨rfl,rfl⟩
    exact no_closed_positive_spine _ (Relation.TransGen.head' hef hbe)

theorem path_after_cut_survives {n : ℕ} {G : PennyGraph n}
    {e f a : OrientedEdge G} (hef : PositiveCellStep e f)
    (hfa : Relation.ReflTransGen PositiveCellStep f a) :
    Relation.ReflTransGen (PositiveSpineCutStep e f) f a := by
  induction hfa with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hfa hab ih =>
    apply ih.tail
    refine ⟨hab,?_⟩
    rintro ⟨rfl,rfl⟩
    exact no_closed_positive_spine _ (Relation.TransGen.head' hef hfa)

def spineVertices {n : ℕ} {G : PennyGraph n} (s t : OrientedEdge G) : Finset (OrientedEdge G) :=
  Finset.univ.filter (OnSpine s t)

theorem spine_cut_partition {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hef : PositiveCellStep e f) (hft : Relation.ReflTransGen PositiveCellStep f t) :
    spineVertices s t=spineVertices s e ∪ spineVertices f t := by
  have hu : Relator.RightUnique (PositiveCellStep (G := G)) :=
    fun _ _ _ h₁ h₂ => positive_step_functional ht h₁ h₂
  ext a
  simp only [spineVertices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨hsa,hat⟩
    rcases Relation.ReflTransGen.total_of_right_unique hu hsa hse with hae | hea
    · exact Or.inl ⟨hsa,hae⟩
    · rcases hea.cases_head with h | ⟨g,heg,hga⟩
      · subst a
        exact Or.inl ⟨hse,Relation.ReflTransGen.refl⟩
      · have hh := positive_step_functional ht hef heg
        exact Or.inr ⟨by simpa only [hh] using hga,hat⟩
  · rintro (⟨hsa,hae⟩ | ⟨hfa,hat⟩)
    · exact ⟨hsa,(hae.tail hef).trans hft⟩
    · exact ⟨(hse.tail hef).trans hfa,hat⟩

theorem spine_cut_disjoint {n : ℕ} {G : PennyGraph n}
    {s t e f : OrientedEdge G} (hef : PositiveCellStep e f) :
    _root_.Disjoint (spineVertices s e) (spineVertices f t) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hae := (Finset.mem_filter.mp ha).2.2
  have hfa := (Finset.mem_filter.mp hb).2.1
  exact no_closed_positive_spine e (Relation.TransGen.head' hef (hfa.trans hae))

theorem spine_cut_edge_count {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hef : PositiveCellStep e f) (hft : Relation.ReflTransGen PositiveCellStep f t) :
    (spineVertices s t).card=(spineVertices s e).card+(spineVertices f t).card := by
  rw [spine_cut_partition ht hse hef hft,Finset.card_union_of_disjoint (spine_cut_disjoint hef)]

def spineCutPieces {n : ℕ} {G : PennyGraph n} (s t e f : OrientedEdge G) :
    Finset (SpineCutComponent e f) := (spineVertices s t).image (spineCutComponent e f)

theorem spineCutPieces_eq_pair {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hef : PositiveCellStep e f) (hft : Relation.ReflTransGen PositiveCellStep f t) :
    spineCutPieces s t e f={spineCutComponent e f e,spineCutComponent e f f} := by
  ext q
  simp only [spineCutPieces,Finset.mem_image,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨a,ha,rfl⟩
    rw [spine_cut_partition ht hse hef hft] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · left
      apply Quotient.sound
      exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
        (path_before_cut_survives hef (Finset.mem_filter.mp ha).2.2)
    · right
      apply Eq.symm
      apply Quotient.sound
      exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
        (path_after_cut_survives hef (Finset.mem_filter.mp ha).2.1)
  · rintro (rfl | rfl)
    · exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hse,(Relation.ReflTransGen.single hef).trans hft⟩,rfl⟩
    · exact ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hse.tail hef,hft⟩,rfl⟩

theorem spineCutPieces_card {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hef : PositiveCellStep e f) (hft : Relation.ReflTransGen PositiveCellStep f t) :
    (spineCutPieces s t e f).card=2 := by
  rw [spineCutPieces_eq_pair ht hse hef hft,Finset.card_pair (cut_step_endpoints_disconnected ht hef)]

end Swanepoel
