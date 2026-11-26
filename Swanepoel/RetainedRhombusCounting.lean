module
public import Swanepoel.JoinClosedCrossings
public import Swanepoel.GeometricCounting
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.retainedRhombi {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) : Finset (RhombusSet G) :=
  Finset.univ.filter (fun R => edgeComponent R.representative.edgeAB∈A ∧
    edgeComponent R.representative.edgeAD∈A)

def PennyGraph.rhombusIndexPair {n : ℕ} (G : PennyGraph n) (R : RhombusSet G) :
    Fin (Fintype.card (TrackComponent G))×Fin (Fintype.card (TrackComponent G)) :=
  let E := Fintype.equivFin (TrackComponent G)
  let a := E (edgeComponent R.representative.edgeAB)
  let b := E (edgeComponent R.representative.edgeAD)
  if a<b then (a,b) else (b,a)

theorem PennyGraph.rhombusIndexPair_unordered {n : ℕ} (G : PennyGraph n) (R : RhombusSet G) :
    s((G.rhombusIndexPair R).1,(G.rhombusIndexPair R).2)=
      s((Fintype.equivFin (TrackComponent G)) (edgeComponent R.representative.edgeAB),
        (Fintype.equivFin (TrackComponent G)) (edgeComponent R.representative.edgeAD)) := by
  dsimp only [rhombusIndexPair]
  split_ifs
  · rfl
  · exact Sym2.eq_swap

theorem PennyGraph.rhombusIndexPair_lt {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (R : RhombusSet G) : (G.rhombusIndexPair R).1<(G.rhombusIndexPair R).2 := by
  have hne : (Fintype.equivFin (TrackComponent G)) (edgeComponent R.representative.edgeAB)≠
      (Fintype.equivFin (TrackComponent G)) (edgeComponent R.representative.edgeAD) :=
    fun h => R.representative.trackPair_ne ht ((Fintype.equivFin (TrackComponent G)).injective h)
  dsimp only [rhombusIndexPair]
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)

theorem PennyGraph.rhombusIndexPair_crosses {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (R : RhombusSet G) : ComponentCrosses
      ((Fintype.equivFin (TrackComponent G)).symm (G.rhombusIndexPair R).1)
      ((Fintype.equivFin (TrackComponent G)).symm (G.rhombusIndexPair R).2) := by
  have hc : ComponentCrosses (edgeComponent R.representative.edgeAB)
      (edgeComponent R.representative.edgeAD) := ⟨R.representative,Or.inl ⟨rfl,rfl⟩⟩
  dsimp only [rhombusIndexPair]
  split_ifs <;> simp only [Equiv.symm_apply_apply]
  · exact hc
  · exact (componentGraph G ht).adj_symm hc

theorem PennyGraph.rhombusIndexPair_injective {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    Function.Injective G.rhombusIndexPair := by
  intro R S h
  have hp := (G.rhombusIndexPair_unordered R).symm.trans
    ((congrArg (fun p => s(p.1,p.2)) h).trans (G.rhombusIndexPair_unordered S))
  apply rhombusCrossingMap_injective G ht
  apply Subtype.ext
  change R.representative.trackPair=S.representative.trackPair
  rcases Sym2.eq_iff.mp hp with hp | hp
  · exact Sym2.eq_iff.mpr (Or.inl ⟨(Fintype.equivFin _).injective hp.1,(Fintype.equivFin _).injective hp.2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨(Fintype.equivFin _).injective hp.1,(Fintype.equivFin _).injective hp.2⟩)

theorem PennyGraph.rhombusIndexPair_exists {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (p : Fin (Fintype.card (TrackComponent G))×Fin (Fintype.card (TrackComponent G)))
    (hp : p.1<p.2) (hc : ComponentCrosses ((Fintype.equivFin (TrackComponent G)).symm p.1)
      ((Fintype.equivFin (TrackComponent G)).symm p.2)) :
    ∃ R : RhombusSet G,G.rhombusIndexPair R=p := by
  let E := Fintype.equivFin (TrackComponent G)
  obtain ⟨C,hC⟩ := hc
  let R : RhombusSet G := ⟨C.corners,⟨C,rfl⟩⟩
  have hpair := R.representative.trackPair_of_corners ht C R.representative_corners
  have hindex := congrArg (Sym2.map E) hpair
  change s(E (edgeComponent R.representative.edgeAB),E (edgeComponent R.representative.edgeAD))=
    s(E (edgeComponent C.edgeAB),E (edgeComponent C.edgeAD)) at hindex
  have htarget : s(E (edgeComponent R.representative.edgeAB),E (edgeComponent R.representative.edgeAD))=s(p.1,p.2) := by
    rcases hC with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simpa only [ha,hb,E,Equiv.apply_symm_apply] using hindex
    · have hrev : s(E (edgeComponent R.representative.edgeAB),E (edgeComponent R.representative.edgeAD))=s(p.2,p.1) := by
        simpa only [ha,hb,E,Equiv.apply_symm_apply] using hindex
      exact hrev.trans Sym2.eq_swap
  have hh := (G.rhombusIndexPair_unordered R).trans htarget
  refine ⟨R,?_⟩
  rcases Sym2.eq_iff.mp hh with h | h
  · exact Prod.ext h.1 h.2
  · have hord := G.rhombusIndexPair_lt ht R
    rw [h.1,h.2] at hord
    exact False.elim (not_lt_of_ge hp.le hord)

theorem PennyGraph.rhombusIndexPair_mem_iff {n : ℕ} (G : PennyGraph n)
    (A : Finset (TrackComponent G)) (R : RhombusSet G) :
    R∈G.retainedRhombi A ↔
      (G.rhombusIndexPair R).1∈A.map (Fintype.equivFin (TrackComponent G)).toEmbedding ∧
      (G.rhombusIndexPair R).2∈A.map (Fintype.equivFin (TrackComponent G)).toEmbedding := by
  dsimp only [retainedRhombi,rhombusIndexPair]
  split_ifs <;> simp only [Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_map_equiv,Equiv.symm_apply_apply]
  exact and_comm

theorem PennyGraph.retainedRhombi_card {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (A : Finset (TrackComponent G)) : (G.retainedRhombi A).card=
      (componentSystem G ht ∅ 0).internal (A.map (Fintype.equivFin (TrackComponent G)).toEmbedding) := by
  change (G.retainedRhombi A).card=
    (((A.map (Fintype.equivFin (TrackComponent G)).toEmbedding).product
      (A.map (Fintype.equivFin (TrackComponent G)).toEmbedding)).filter
      (fun p => p.1<p.2 ∧ ComponentCrosses ((Fintype.equivFin (TrackComponent G)).symm p.1)
        ((Fintype.equivFin (TrackComponent G)).symm p.2))).card
  refine Finset.card_bij (fun R _ => G.rhombusIndexPair R) ?_ ?_ ?_
  · intro R hR
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ((G.rhombusIndexPair_mem_iff A R).mp hR),
      G.rhombusIndexPair_lt ht R,G.rhombusIndexPair_crosses ht R⟩
  · intro R _ S _ h
    exact G.rhombusIndexPair_injective ht h
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨R,hR⟩ := G.rhombusIndexPair_exists ht p hp'.2.1 hp'.2.2
    exact ⟨R,(G.rhombusIndexPair_mem_iff A R).mpr (by rw [hR]; exact Finset.mem_product.mp hp'.1),hR⟩

theorem PennyGraph.retained_family_rhombi_card {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : (G.retainedRhombi (G.familyTrackComponents Y)).card=
      G.familyInternalCrossings ht Y := G.retainedRhombi_card ht _

end Swanepoel
