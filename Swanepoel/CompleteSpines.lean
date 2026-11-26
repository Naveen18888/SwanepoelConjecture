module
public import Swanepoel.PositiveSpines
@[expose] public section

noncomputable section
namespace Swanepoel

def RhombusCell.backwards {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : RhombusCell G where
  a := C.d
  b := C.c
  c := C.b
  d := C.a
  ac := C.bd.symm
  bd := C.ac.symm
  ab := C.cd.symm
  bc := C.bc.symm
  cd := C.ab.symm
  da := C.da.symm

theorem cellStep_oriented {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (h : CellStep e f) : PositiveCellStep e f ∨ PositiveCellStep f e := by
  obtain ⟨C,he,hf⟩ := h
  by_cases hp : 0 < cross2 C.u C.v
  · exact Or.inl ⟨C,he,hf,hp⟩
  · have hn : cross2 C.u C.v < 0 := by
      have ha := C.area_lower ht
      rw [abs_of_nonpos (le_of_not_gt hp)] at ha
      have hs := Real.sqrt_nonneg (3 : ℝ)
      linarith
    have hu : C.backwards.u=C.u := C.opposite_vectors.symm
    have hv : C.backwards.v= -C.v := by
      change G.point C.a-G.point C.d= -(G.point C.d-G.point C.a)
      abel
    refine Or.inr ⟨C.backwards,?_,?_,?_⟩
    · simpa only [RhombusCell.backwards] using hf
    · simpa only [RhombusCell.backwards] using he
    · rw [hu,hv]
      have hx : cross2 C.u (-C.v)= -cross2 C.u C.v := by
        unfold cross2
        change C.u 0 * (-C.v 1)-C.u 1 * (-C.v 0)= -(C.u 0*C.v 1-C.u 1*C.v 0)
        ring
      rw [hx]
      linarith

def OnSpine {n : ℕ} {G : PennyGraph n} (s t e : OrientedEdge G) : Prop :=
  Relation.ReflTransGen PositiveCellStep s e ∧ Relation.ReflTransGen PositiveCellStep e t

def OnUnorientedSpine {n : ℕ} {G : PennyGraph n} (s t e : OrientedEdge G) : Prop :=
  OnSpine s t e ∨ OnSpine (reverseEdge t) (reverseEdge s) e

theorem spine_prefix_closed {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s e f : OrientedEdge G} (hs : ¬ ∃ g, PositiveCellStep g s)
    (hse : Relation.ReflTransGen PositiveCellStep s e) (hfe : PositiveCellStep f e) :
    Relation.ReflTransGen PositiveCellStep s f := by
  rcases hse.cases_tail with h | ⟨p,hsp,hpe⟩
  · subst e
    exact False.elim (hs ⟨f,hfe⟩)
  · have hh := positive_step_injective ht hfe hpe
    subst f
    exact hsp

theorem spine_suffix_closed {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {t e f : OrientedEdge G} (htop : ¬ ∃ g, PositiveCellStep t g)
    (het : Relation.ReflTransGen PositiveCellStep e t) (hef : PositiveCellStep e f) :
    Relation.ReflTransGen PositiveCellStep f t := by
  rcases het.cases_head with h | ⟨p,hep,hpt⟩
  · subst e
    exact False.elim (htop ⟨f,hef⟩)
  · have hh := positive_step_functional ht hef hep
    subst f
    exact hpt

theorem onSpine_positive_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hs : ¬ ∃ g, PositiveCellStep g s)
    (htop : ¬ ∃ g, PositiveCellStep t g) (hef : PositiveCellStep e f) :
    OnSpine s t e ↔ OnSpine s t f := by
  constructor
  · rintro ⟨hse,het⟩
    exact ⟨hse.tail hef,spine_suffix_closed ht htop het hef⟩
  · rintro ⟨hsf,hft⟩
    exact ⟨spine_prefix_closed ht hs hsf hef,(Relation.ReflTransGen.single hef).trans hft⟩

theorem onSpine_cell_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hs : ¬ ∃ g, PositiveCellStep g s)
    (htop : ¬ ∃ g, PositiveCellStep t g) (hef : CellStep e f) :
    OnSpine s t e ↔ OnSpine s t f := by
  rcases cellStep_oriented ht hef with h | h
  · exact onSpine_positive_iff ht hs htop h
  · exact (onSpine_positive_iff ht hs htop h).symm

theorem OnSpine.reverse {n : ℕ} {G : PennyGraph n} {s t e : OrientedEdge G}
    (h : OnSpine s t e) : OnSpine (reverseEdge t) (reverseEdge s) (reverseEdge e) :=
  ⟨positive_path_reverse h.2,positive_path_reverse h.1⟩

theorem OnUnorientedSpine.reverse {n : ℕ} {G : PennyGraph n} {s t e : OrientedEdge G}
    (h : OnUnorientedSpine s t e) : OnUnorientedSpine s t (reverseEdge e) := by
  rcases h with h | h
  · exact Or.inr h.reverse
  · left
    simpa only [reverseEdge_involutive] using h.reverse

theorem unoriented_cell_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hs : ¬ ∃ g, PositiveCellStep g s)
    (htop : ¬ ∃ g, PositiveCellStep t g) (hef : CellStep e f) :
    OnUnorientedSpine s t e ↔ OnUnorientedSpine s t f := by
  have hsrev : ¬ ∃ g, PositiveCellStep g (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have htrev : ¬ ∃ g, PositiveCellStep (reverseEdge s) g := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact hs ⟨reverseEdge g,hh⟩
  exact or_congr (onSpine_cell_iff ht hs htop hef) (onSpine_cell_iff ht hsrev htrev hef)

theorem unoriented_track_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t e f : OrientedEdge G} (hs : ¬ ∃ g, PositiveCellStep g s)
    (htop : ¬ ∃ g, PositiveCellStep t g) (hef : Relation.EqvGen TrackStep e f) :
    OnUnorientedSpine s t e ↔ OnUnorientedSpine s t f := by
  induction hef with
  | rel e f h =>
    rcases h with h | rfl
    · exact unoriented_cell_iff ht hs htop h
    · exact ⟨OnUnorientedSpine.reverse,fun h => by
        simpa only [reverseEdge_involutive] using h.reverse⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem component_complete_spine {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (e : OrientedEdge G) : ∃ s t,
      (¬ ∃ g, PositiveCellStep g s) ∧ (¬ ∃ g, PositiveCellStep t g) ∧
      OnSpine s t e ∧
      ∀ f, edgeComponent f=edgeComponent e → OnUnorientedSpine s t f := by
  obtain ⟨s,hse,hs⟩ := exists_spine_start e
  obtain ⟨t,het,htop⟩ := exists_spine_end e
  refine ⟨s,t,hs,htop,⟨hse,het⟩,?_⟩
  intro f hf
  exact (unoriented_track_iff ht hs htop (Quotient.exact hf)).mpr (Or.inl ⟨hse,het⟩)

theorem positive_path_component {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.ReflTransGen PositiveCellStep e f) : edgeComponent e=edgeComponent f := by
  induction h with
  | refl => rfl
  | tail _ h ih =>
    exact ih.trans (Quotient.sound (Relation.EqvGen.rel _ _ (Or.inl h.to_cellStep)))

theorem reverse_component {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    edgeComponent e=edgeComponent (reverseEdge e) :=
  Quotient.sound (Relation.EqvGen.rel _ _ (Or.inr rfl))

theorem onUnorientedSpine_component {n : ℕ} {G : PennyGraph n} {s t e f : OrientedEdge G}
    (he : OnSpine s t e) (hf : OnUnorientedSpine s t f) :
    edgeComponent f=edgeComponent e := by
  rcases hf with hf | hf
  · exact (positive_path_component hf.1).symm.trans (positive_path_component he.1)
  · exact (positive_path_component hf.1).symm.trans
      ((reverse_component t).symm.trans (positive_path_component he.2).symm)

theorem component_spine_iff {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (e : OrientedEdge G) : ∃ s t,
      (¬ ∃ g, PositiveCellStep g s) ∧ (¬ ∃ g, PositiveCellStep t g) ∧
      OnSpine s t e ∧
      ∀ f, edgeComponent f=edgeComponent e ↔ OnUnorientedSpine s t f := by
  obtain ⟨s,t,hs,htop,he,hall⟩ := component_complete_spine ht e
  exact ⟨s,t,hs,htop,he,fun f => ⟨hall f,onUnorientedSpine_component he⟩⟩

end Swanepoel
