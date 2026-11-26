module
public import Swanepoel.SingleCrossings
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def RhombusCell.edgeBC {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : OrientedEdge G :=
  ⟨(C.b,C.c),C.bc⟩
def RhombusCell.edgeCD {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : OrientedEdge G :=
  ⟨(C.c,C.d),C.cd⟩
def RhombusCell.edgeDA {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : OrientedEdge G :=
  ⟨(C.d,C.a),C.da⟩

theorem edgeComponent_of_unordered_eq {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G)
    (h : s(e.val.1,e.val.2)=s(f.val.1,f.val.2)) : edgeComponent e=edgeComponent f := by
  rcases Sym2.eq_iff.mp h with h | h
  · have he : e=f := Subtype.ext (Prod.ext h.1 h.2)
    rw [he]
  · have he : e=reverseEdge f := Subtype.ext (Prod.ext h.1 h.2)
    rw [he]
    exact (reverse_component f).symm

theorem RhombusCell.component_dc {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    edgeComponent C.edgeDC=edgeComponent C.edgeAB := by
  have h : Relation.EqvGen TrackStep C.edgeAB C.edgeDC :=
    Relation.EqvGen.rel _ _ (Or.inl ⟨C,rfl,rfl⟩)
  exact (show edgeComponent C.edgeAB=edgeComponent C.edgeDC from Quotient.sound h).symm

theorem RhombusCell.component_bc {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    edgeComponent C.edgeBC=edgeComponent C.edgeAD := by
  have h : Relation.EqvGen TrackStep C.edgeAD C.edgeBC :=
    Relation.EqvGen.rel _ _ (Or.inl ⟨C.transpose,rfl,rfl⟩)
  exact (show edgeComponent C.edgeAD=edgeComponent C.edgeBC from Quotient.sound h).symm

theorem RhombusCell.component_cd {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    edgeComponent C.edgeCD=edgeComponent C.edgeAB := by
  have h : C.edgeCD=reverseEdge C.edgeDC := by apply Subtype.ext; rfl
  rw [h]
  exact (reverse_component C.edgeDC).symm.trans C.component_dc

theorem RhombusCell.component_da {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) :
    edgeComponent C.edgeDA=edgeComponent C.edgeAD := by
  have h : C.edgeDA=reverseEdge C.edgeAD := by apply Subtype.ext; rfl
  rw [h]
  exact (reverse_component C.edgeAD).symm

theorem RhombusCell.adj_inside {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) (x y : Fin n) (hx : x ∈ C.corners) (hy : y ∈ C.corners)
    (hxy : G.graph.Adj x y) :
    s(x,y)=s(C.a,C.b) ∨ s(x,y)=s(C.b,C.c) ∨ s(x,y)=s(C.c,C.d) ∨ s(x,y)=s(C.d,C.a) := by
  have hac : ¬ G.graph.Adj C.a C.c := fun h => ht C.a C.b C.c C.ab C.bc h.symm
  have hbd : ¬ G.graph.Adj C.b C.d := fun h => ht C.b C.c C.d C.bc C.cd h.symm
  simp only [RhombusCell.corners,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hxy.ne rfl)
    | exact False.elim (hac hxy)
    | exact False.elim (hac hxy.symm)
    | exact False.elim (hbd hxy)
    | exact False.elim (hbd hxy.symm)
    | simp

theorem RhombusCell.inside_component {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) (e : OrientedEdge G)
    (he1 : e.val.1 ∈ C.corners) (he2 : e.val.2 ∈ C.corners) :
    edgeComponent e=edgeComponent C.edgeAB ∨ edgeComponent e=edgeComponent C.edgeAD := by
  rcases C.adj_inside ht _ _ he1 he2 e.property with h | h | h | h
  · exact Or.inl (edgeComponent_of_unordered_eq e C.edgeAB h)
  · exact Or.inr ((edgeComponent_of_unordered_eq e C.edgeBC h).trans C.component_bc)
  · exact Or.inl ((edgeComponent_of_unordered_eq e C.edgeCD h).trans C.component_cd)
  · exact Or.inr ((edgeComponent_of_unordered_eq e C.edgeDA h).trans C.component_da)

def RhombusCell.trackPair {n : ℕ} {G : PennyGraph n} (C : RhombusCell G) : Sym2 (TrackComponent G) :=
  s(edgeComponent C.edgeAB,edgeComponent C.edgeAD)

theorem RhombusCell.trackPair_ne {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)
    (ht : G.TriangleFree) : edgeComponent C.edgeAB ≠ edgeComponent C.edgeAD :=
  (componentGraph G ht).ne_of_adj ⟨C,Or.inl ⟨rfl,rfl⟩⟩

theorem RhombusCell.trackPair_of_corners {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (C D : RhombusCell G) (hc : C.corners=D.corners) : C.trackPair=D.trackPair := by
  have hdA : D.a ∈ C.corners := by rw [hc]; simp [RhombusCell.corners]
  have hdB : D.b ∈ C.corners := by rw [hc]; simp [RhombusCell.corners]
  have hdD : D.d ∈ C.corners := by rw [hc]; simp [RhombusCell.corners]
  have h1 := C.inside_component ht D.edgeAB hdA hdB
  have h2 := C.inside_component ht D.edgeAD hdA hdD
  have hne := D.trackPair_ne ht
  unfold RhombusCell.trackPair
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact False.elim (hne (h1.trans h2.symm))
  · rw [h1,h2]
  · rw [h1,h2]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)
  · exact False.elim (hne (h1.trans h2.symm))

abbrev RhombusSet {n : ℕ} (G : PennyGraph n) :=
  {S : Finset (Fin n) // ∃ C : RhombusCell G, C.corners=S}

noncomputable instance {n : ℕ} (G : PennyGraph n) : Fintype (RhombusSet G) := Fintype.ofFinite _

def RhombusSet.representative {n : ℕ} {G : PennyGraph n} (R : RhombusSet G) : RhombusCell G :=
  Classical.choose R.property

theorem RhombusSet.representative_corners {n : ℕ} {G : PennyGraph n} (R : RhombusSet G) :
    R.representative.corners=R.val := Classical.choose_spec R.property

def rhombusCrossingMap {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (R : RhombusSet G) : (componentGraph G ht).edgeSet := by
  refine ⟨R.representative.trackPair,?_⟩
  exact ⟨R.representative,Or.inl ⟨rfl,rfl⟩⟩

theorem rhombusCrossingMap_injective {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Function.Injective (rhombusCrossingMap G ht) := by
  intro R S h
  have he := congrArg Subtype.val h
  change R.representative.trackPair=S.representative.trackPair at he
  have hm :
      (edgeComponent S.representative.edgeAB=edgeComponent R.representative.edgeAB ∧
        edgeComponent S.representative.edgeAD=edgeComponent R.representative.edgeAD) ∨
      (edgeComponent S.representative.edgeAB=edgeComponent R.representative.edgeAD ∧
        edgeComponent S.representative.edgeAD=edgeComponent R.representative.edgeAB) := by
    rcases Sym2.eq_iff.mp he with h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.2.symm,h.1.symm⟩
  have hc := rhombi_single_crossing ht R.representative S.representative
    (edgeComponent R.representative.edgeAB) (edgeComponent R.representative.edgeAD)
    (Or.inl ⟨rfl,rfl⟩) hm
  exact Subtype.ext (R.representative_corners.symm.trans (hc.trans S.representative_corners))

theorem rhombusCrossingMap_surjective {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Function.Surjective (rhombusCrossingMap G ht) := by
  rintro ⟨z,hz⟩
  revert hz
  refine Sym2.inductionOn z ?_
  intro t u htu
  change ComponentCrosses t u at htu
  obtain ⟨C,hC⟩ := htu
  let R : RhombusSet G := ⟨C.corners,⟨C,rfl⟩⟩
  refine ⟨R,?_⟩
  apply Subtype.ext
  change R.representative.trackPair=s(t,u)
  have hp := RhombusCell.trackPair_of_corners ht R.representative C R.representative_corners
  rw [hp]
  rcases hC with ⟨he,hf⟩ | ⟨he,hf⟩
  · simp only [RhombusCell.trackPair,he,hf]
  · simp only [RhombusCell.trackPair,he,hf]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)

theorem rhombus_count_eq_crossings {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Fintype.card (RhombusSet G)=(componentGraph G ht).edgeFinset.card := by
  have h := Fintype.card_congr (Equiv.ofBijective (rhombusCrossingMap G ht)
    ⟨rhombusCrossingMap_injective G ht,rhombusCrossingMap_surjective G ht⟩)
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using h

end Swanepoel
