module
public import Swanepoel.DirectionPacking
public import Swanepoel.Tracks
@[expose] public section

noncomputable section
namespace Swanepoel

def reverseEdge {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : OrientedEdge G :=
  ⟨(e.val.2,e.val.1),e.property.symm⟩

theorem reverseEdge_vector {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    carriedVector (reverseEdge e)= -carriedVector e := by
  dsimp [reverseEdge,carriedVector]
  abel

theorem carriedVector_norm {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    ‖carriedVector e‖=1 := by
  simpa only [carriedVector, ← dist_eq_norm] using e.property.symm.2

def TrackStep {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) : Prop :=
  CellStep e f ∨ f=reverseEdge e

theorem trackStep_sameLine {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : TrackStep e f) : SameLine (carriedVector e) (carriedVector f) := by
  rcases h with h | rfl
  · exact Or.inl h.vector_eq
  · right
    rw [reverseEdge_vector,neg_neg]

theorem generated_track_sameLine {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.EqvGen TrackStep e f) : SameLine (carriedVector e) (carriedVector f) := by
  induction h with
  | rel _ _ h => exact trackStep_sameLine h
  | refl => exact SameLine.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

abbrev TrackComponent {n : ℕ} (G : PennyGraph n) :=
  Quotient (Relation.EqvGen.setoid (TrackStep (G := G)))

noncomputable instance {n : ℕ} (G : PennyGraph n) : Fintype (TrackComponent G) :=
  Fintype.ofFinite _

def edgeComponent {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : TrackComponent G :=
  Quotient.mk _ e

def componentVector {n : ℕ} {G : PennyGraph n} (t : TrackComponent G) : Plane :=
  carriedVector t.out

theorem componentVector_norm {n : ℕ} {G : PennyGraph n} (t : TrackComponent G) :
    ‖componentVector t‖=1 := carriedVector_norm t.out

theorem component_sameLine {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G)
    (t : TrackComponent G) (he : edgeComponent e=t) :
    SameLine (carriedVector e) (componentVector t) := by
  have hq : edgeComponent e=edgeComponent t.out := he.trans (Quotient.out_eq t).symm
  exact generated_track_sameLine (Quotient.exact hq)

def RhombusCell.edgeAB {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : OrientedEdge G :=
  ⟨(C.a,C.b),C.ab⟩

def RhombusCell.edgeAD {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : OrientedEdge G :=
  ⟨(C.a,C.d),C.da.symm⟩

def ComponentCrosses {n : ℕ} {G : PennyGraph n} (t u : TrackComponent G) : Prop :=
  ∃ C : RhombusCell G,
    (edgeComponent C.edgeAB=t ∧ edgeComponent C.edgeAD=u) ∨
    (edgeComponent C.edgeAB=u ∧ edgeComponent C.edgeAD=t)

theorem component_crossing_angle {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {t u : TrackComponent G} (h : ComponentCrosses t u) :
    |inner ℝ (componentVector t) (componentVector u)| < 1/2 := by
  obtain ⟨C,h⟩ := h
  rcases h with ⟨he,hf⟩ | ⟨he,hf⟩
  · have hl := (component_sameLine C.edgeAB t he).abs_inner_eq
      (component_sameLine C.edgeAD u hf)
    rw [← hl]
    exact C.abs_inner_lt_half ht
  · have hl := (component_sameLine C.edgeAB u he).abs_inner_eq
      (component_sameLine C.edgeAD t hf)
    have ha : |inner ℝ (componentVector u) (componentVector t)| < 1/2 := by
      rw [← hl]
      exact C.abs_inner_lt_half ht
    simpa only [real_inner_comm] using ha

def componentGraph {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    SimpleGraph (TrackComponent G) where
  Adj := ComponentCrosses
  symm := ⟨by intro t u h; obtain ⟨C,h⟩ := h; exact ⟨C,h.symm⟩⟩
  loopless := ⟨by
    intro t h
    have ha := component_crossing_angle ht h
    rw [real_inner_self_eq_norm_sq,componentVector_norm] at ha
    norm_num at ha⟩

theorem componentGraph_noTriple {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    ∀ t u v, (componentGraph G ht).Adj t u → (componentGraph G ht).Adj u v →
      ¬ (componentGraph G ht).Adj v t := by
  intro t u v htu huv hvt
  exact no_three_separated_unit_directions _ _ _
    (componentVector_norm t) (componentVector_norm u) (componentVector_norm v)
    (component_crossing_angle ht htu) (component_crossing_angle ht huv)
    (component_crossing_angle ht hvt)

def componentSystem {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (ordinary : Finset (TrackComponent G)) (defects : ℕ) : TrackSystem where
  count := Fintype.card (TrackComponent G)
  ordinary := ordinary.map (Fintype.equivFin (TrackComponent G)).toEmbedding
  crossing := (componentGraph G ht).comap (Fintype.equivFin (TrackComponent G)).symm
  defects := defects

theorem componentSystem_noTriple {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (ordinary : Finset (TrackComponent G)) (defects : ℕ) :
    (componentSystem G ht ordinary defects).NoTriple := by
  intro t u v htu huv hvt
  exact componentGraph_noTriple G ht _ _ _ htu huv hvt

end Swanepoel
