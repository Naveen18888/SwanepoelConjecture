module
public import Swanepoel.BlockTrackLeafGraph
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem RhombusCell.leaf_not_mem_corners {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a) : v∉C.corners := by
  intro hv
  simp only [RhombusCell.corners,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv | hv
  · exact C.bd ((hunique C.b (by rw [hv]; exact C.ab)).trans
      (hunique C.d (by rw [hv]; exact C.da.symm)).symm)
  · exact C.ac ((hunique C.a (by rw [hv]; exact C.ab.symm)).trans
      (hunique C.c (by rw [hv]; exact C.bc)).symm)
  · exact C.bd ((hunique C.b (by rw [hv]; exact C.bc.symm)).trans
      (hunique C.d (by rw [hv]; exact C.cd)).symm)
  · exact C.ac ((hunique C.a (by rw [hv]; exact C.da)).trans
      (hunique C.c (by rw [hv]; exact C.cd.symm)).symm)

theorem RhombusCell.leaf_corners_ne {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a) :
    C.a≠v ∧ C.b≠v ∧ C.c≠v ∧ C.d≠v := by
  have hn := C.leaf_not_mem_corners v a hunique
  refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> apply hn
  · exact h ▸ (by simp [RhombusCell.corners] : C.a∈C.corners)
  · exact h ▸ (by simp [RhombusCell.corners] : C.b∈C.corners)
  · exact h ▸ (by simp [RhombusCell.corners] : C.c∈C.corners)
  · exact h ▸ (by simp [RhombusCell.corners] : C.d∈C.corners)

namespace PennyGraph
variable {n : ℕ} (G : PennyGraph n)

def leafContact (v a : Fin n) (ha : G.graph.Adj v a) : OrientedEdge G := ⟨(v,a),ha⟩

def leafTrack (v a : Fin n) (ha : G.graph.Adj v a) : TrackComponent G := edgeComponent (G.leafContact v a ha)

theorem trackStep_avoids_leaf_iff (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    {e f : OrientedEdge G} (h : TrackStep e f) :
    (e.val.1≠v ∧ e.val.2≠v) ↔ (f.val.1≠v ∧ f.val.2≠v) := by
  rcases h with ⟨C,he,hf⟩ | rfl
  · have hn := C.leaf_corners_ne v a hunique
    rw [he,hf]
    exact ⟨fun _ => ⟨hn.2.2.2,hn.2.2.1⟩,fun _ => ⟨hn.1,hn.2.1⟩⟩
  · change (e.val.1≠v ∧ e.val.2≠v) ↔ (e.val.2≠v ∧ e.val.1≠v)
    exact and_comm

theorem trackComponent_avoids_leaf_iff (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (e f : OrientedEdge G) (hcomp : edgeComponent e=edgeComponent f) :
    (e.val.1≠v ∧ e.val.2≠v) ↔ (f.val.1≠v ∧ f.val.2≠v) := by
  have h := Quotient.exact hcomp
  clear hcomp
  induction h with
  | rel e f h => exact G.trackStep_avoids_leaf_iff v a hunique h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem touching_leaf_component (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) (e : OrientedEdge G)
    (he : e.val.1=v ∨ e.val.2=v) : edgeComponent e=G.leafTrack v a ha := by
  rcases he with h | h
  · have hb : e.val.2=a := hunique _ (h ▸ e.property)
    have heq : e=G.leafContact v a ha := Subtype.ext (Prod.ext h hb)
    rw [heq]
    rfl
  · have hb : e.val.1=a := hunique _ (h ▸ e.property.symm)
    have heq : e=reverseEdge (G.leafContact v a ha) := Subtype.ext (Prod.ext hb h)
    rw [heq]
    exact (reverse_component (G.leafContact v a ha)).symm

theorem edge_avoids_leaf_iff (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) (e : OrientedEdge G) :
    (e.val.1≠v ∧ e.val.2≠v) ↔ edgeComponent e≠G.leafTrack v a ha := by
  constructor
  · intro he hcomp
    have hl := (G.trackComponent_avoids_leaf_iff v a hunique e (G.leafContact v a ha) hcomp).mp he
    exact hl.1 rfl
  · intro hn
    constructor
    · intro h
      exact hn (G.touching_leaf_component v a ha hunique e (Or.inl h))
    · intro h
      exact hn (G.touching_leaf_component v a ha hunique e (Or.inr h))

def eraseComponentMap (v : Fin n) : TrackComponent (G.eraseVertex v)→TrackComponent G :=
  (G.eraseVertexEmbedding v).componentMap

@[simp] theorem eraseComponentMap_edge (v : Fin n) (e : OrientedEdge (G.eraseVertex v)) :
    G.eraseComponentMap v (edgeComponent e)=edgeComponent ((G.eraseVertexEmbedding v).mapEdge e) := rfl

theorem eraseComponentMap_injective (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a) :
    Function.Injective (G.eraseComponentMap v) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro e f hcomp
  change edgeComponent e=edgeComponent f
  apply (G.eraseVertexEmbedding v).component_eq_of_full_retention e f hcomp
  intro b hb
  have havoid : b.val.1≠v ∧ b.val.2≠v :=
    (G.trackComponent_avoids_leaf_iff v a hunique b ((G.eraseVertexEmbedding v).mapEdge e) hb).mpr
      ⟨G.eraseVertexMap_ne v e.val.1,G.eraseVertexMap_ne v e.val.2⟩
  exact ⟨G.eraseLiftEdge v b havoid.1 havoid.2,G.eraseLiftEdge_map v b havoid.1 havoid.2⟩

theorem eraseComponentMap_full_retention (v a : Fin n)
    (hunique : ∀ w,G.graph.Adj v w → w=a) (c : TrackComponent (G.eraseVertex v))
    (e : OrientedEdge G) (he : edgeComponent e=G.eraseComponentMap v c) :
    ∃ f : OrientedEdge (G.eraseVertex v),(G.eraseVertexEmbedding v).mapEdge f=e := by
  revert he
  refine Quotient.inductionOn c ?_
  intro f he
  have havoid := (G.trackComponent_avoids_leaf_iff v a hunique e
    ((G.eraseVertexEmbedding v).mapEdge f) he).mpr
      ⟨G.eraseVertexMap_ne v f.val.1,G.eraseVertexMap_ne v f.val.2⟩
  exact ⟨G.eraseLiftEdge v e havoid.1 havoid.2,G.eraseLiftEdge_map v e havoid.1 havoid.2⟩

theorem eraseComponentMap_image (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) :
    (Finset.univ : Finset (TrackComponent (G.eraseVertex v))).image (G.eraseComponentMap v)=
      (Finset.univ : Finset (TrackComponent G)).erase (G.leafTrack v a ha) := by
  ext c
  constructor
  · intro hc
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    refine Quotient.inductionOn d ?_
    intro e
    exact (G.edge_avoids_leaf_iff v a ha hunique ((G.eraseVertexEmbedding v).mapEdge e)).mp
      ⟨G.eraseVertexMap_ne v e.val.1,G.eraseVertexMap_ne v e.val.2⟩
  · intro hc
    have hc' := Finset.mem_erase.mp hc
    let e := c.out
    have he : edgeComponent e=c := Quotient.out_eq c
    have havoid := (G.edge_avoids_leaf_iff v a ha hunique e).mpr (by rw [he]; exact hc'.1)
    let eH := G.eraseLiftEdge v e havoid.1 havoid.2
    refine Finset.mem_image.mpr ⟨edgeComponent eH,Finset.mem_univ _,?_⟩
    rw [G.eraseComponentMap_edge,G.eraseLiftEdge_map]
    exact he

def eraseLeafCell (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (C : RhombusCell G) : RhombusCell (G.eraseVertex v) :=
  let hn := C.leaf_corners_ne v a hunique
  let hABa : C.edgeAB.val.1≠v := hn.1
  let hABb : C.edgeAB.val.2≠v := hn.2.1
  let hDCd : C.edgeDC.val.1≠v := hn.2.2.2
  let hDCc : C.edgeDC.val.2≠v := hn.2.2.1
  (G.eraseVertexEmbedding v).pullCell
    (G.eraseLiftEdge v C.edgeAB hABa hABb)
    (G.eraseLiftEdge v C.edgeDC hDCd hDCc) C
    (congrArg Subtype.val (G.eraseLiftEdge_map v C.edgeAB hABa hABb))
    (congrArg Subtype.val (G.eraseLiftEdge_map v C.edgeDC hDCd hDCc))

theorem eraseLeafCell_edgeAB (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (C : RhombusCell G) :
    (G.eraseVertexEmbedding v).mapEdge (G.eraseLeafCell v a hunique C).edgeAB=C.edgeAB := by
  have hn := C.leaf_corners_ne v a hunique
  apply Subtype.ext
  change (G.eraseVertexMap v (G.eraseVertexIndex v C.a hn.1),
    G.eraseVertexMap v (G.eraseVertexIndex v C.b hn.2.1))=(C.a,C.b)
  rw [G.eraseVertexMap_index,G.eraseVertexMap_index]

theorem eraseLeafCell_edgeAD (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (C : RhombusCell G) :
    (G.eraseVertexEmbedding v).mapEdge (G.eraseLeafCell v a hunique C).edgeAD=C.edgeAD := by
  have hn := C.leaf_corners_ne v a hunique
  apply Subtype.ext
  change (G.eraseVertexMap v (G.eraseVertexIndex v C.a hn.1),
    G.eraseVertexMap v (G.eraseVertexIndex v C.d hn.2.2.2))=(C.a,C.d)
  rw [G.eraseVertexMap_index,G.eraseVertexMap_index]

theorem eraseComponentMap_crossing_iff (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (c d : TrackComponent (G.eraseVertex v)) :
    ComponentCrosses (G.eraseComponentMap v c) (G.eraseComponentMap v d) ↔ ComponentCrosses c d := by
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨G.eraseLeafCell v a hunique C,?_⟩
    have hf := G.eraseComponentMap_injective v a hunique
    have hab : G.eraseComponentMap v (edgeComponent (G.eraseLeafCell v a hunique C).edgeAB)=edgeComponent C.edgeAB := by
      rw [G.eraseComponentMap_edge,G.eraseLeafCell_edgeAB v a hunique C]
    have had : G.eraseComponentMap v (edgeComponent (G.eraseLeafCell v a hunique C).edgeAD)=edgeComponent C.edgeAD := by
      rw [G.eraseComponentMap_edge,G.eraseLeafCell_edgeAD v a hunique C]
    rcases hC with ⟨hc,hd⟩ | ⟨hc,hd⟩
    · exact Or.inl ⟨hf (hab.trans hc),hf (had.trans hd)⟩
    · exact Or.inr ⟨hf (hab.trans hc),hf (had.trans hd)⟩
  · exact (G.eraseVertexEmbedding v).crossing_map

theorem leafTrack_isolated (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) (c : TrackComponent G) :
    ¬ComponentCrosses (G.leafTrack v a ha) c := by
  rintro ⟨C,hC⟩
  have hn := C.leaf_corners_ne v a hunique
  have hAB := (G.edge_avoids_leaf_iff v a ha hunique C.edgeAB).mp ⟨hn.1,hn.2.1⟩
  have hAD := (G.edge_avoids_leaf_iff v a ha hunique C.edgeAD).mp ⟨hn.1,hn.2.2.2⟩
  exact hC.elim (fun h => hAB h.1) (fun h => hAD h.2)

theorem eraseSource_iff (v a : Fin n) (hunique : ∀ w,G.graph.Adj v w → w=a)
    (e : OrientedEdge (G.eraseVertex v)) :
    SpineSource e ↔ SpineSource ((G.eraseVertexEmbedding v).mapEdge e) := by
  constructor
  · intro he
    rintro ⟨f,hf⟩
    obtain ⟨C,hfC,heC,hpos⟩ := hf
    have hn := C.leaf_corners_ne v a hunique
    have hfA : f.val.1≠v := by simpa only [hfC] using hn.1
    have hfB : f.val.2≠v := by simpa only [hfC] using hn.2.1
    let fH := G.eraseLiftEdge v f hfA hfB
    apply he
    refine ⟨fH,((G.eraseVertexEmbedding v).positive_step_iff fH e).mpr ?_⟩
    rw [G.eraseLiftEdge_map]
    exact ⟨C,hfC,heC,hpos⟩
  · exact (G.eraseVertexEmbedding v).source_of_source_map e

theorem eraseVertex_component_count (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) :
    Fintype.card (TrackComponent (G.eraseVertex v))+1=Fintype.card (TrackComponent G) := by
  have hi := congrArg Finset.card (G.eraseComponentMap_image v a ha hunique)
  rw [Finset.card_image_of_injective _ (G.eraseComponentMap_injective v a hunique),Finset.card_univ] at hi
  have he := Finset.card_erase_add_one (Finset.mem_univ (G.leafTrack v a ha))
  rw [Finset.card_univ] at he
  omega

end PennyGraph
end Swanepoel
