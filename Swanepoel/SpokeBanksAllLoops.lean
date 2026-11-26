module
public import Swanepoel.SpokeCrossingLabels
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem PositiveSpineChain.bankRegion_avoids_pair_loop {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (c d : TrackComponent G) (hmc : ¬ComponentCrosses (edgeComponent s) c)
    (hmd : ¬ComponentCrosses (edgeComponent s) d)
    (F outer : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (houter : ¬Bornology.IsBounded outer.val) {a : Plane} (loop : PlaneChain a a)
    (hloop : G.SpokePairSupport c d F outer loop)
    (sign : ℝ) (hsign : sign=1 ∨ sign= -1) : Disjoint (p.bankRegion sign) loop.trace := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,δ,hδ,rfl⟩ hz
  have hn : sign*δ≠0 := by rcases hsign with rfl | rfl <;> nlinarith only [hδ.1]
  have hb : |sign*δ|≤1/2 := by
    rcases hsign with rfl | rfl <;> simp only [one_mul,neg_mul,abs_neg,abs_of_pos hδ.1] <;> exact hδ.2
  have avoid (cut : TrackComponent G) (hmiss : ¬ComponentCrosses (edgeComponent s) cut) :
      x+(sign*δ) • carriedVector s∉trackSpineTrace cut := by
    by_cases hc : edgeComponent s=cut
    · rw [← hc]
      exact complete_spine_translated_point_not_on_spine ht hs htop p.reach (p.trace_subset_track hx) hn
    · exact p.translated_trace_avoids_noncrossing_spine ht cut hc hmiss hx hb
  rcases hloop hz with ((hc | hd) | hface) | hout
  · exact avoid c hmc hc
  · exact avoid d hmd hd
  · exact p.translated_trace_avoids_defect ht F hF hx hb hface
  · exact p.translated_trace_avoids_outer ht outer houter hx hb hout

theorem PositiveSpineChain.carried_start_mem_bank {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : SpineSource s) (htop : ¬∃g,PositiveCellStep t g)
    (e : OrientedEdge G) (he : edgeComponent e=edgeComponent s) (sign : ℝ)
    (hv : carriedVector e=(-sign) • carriedVector s) : G.point e.val.1∈p.bankRegion sign := by
  have hx : edgeCenter e∈p.toPlane.trace := by
    rw [p.complete_trace ht hs htop]
    exact Or.inl ⟨e,he,rfl⟩
  refine ⟨edgeCenter e,hx,1/2,⟨by norm_num,le_rfl⟩,?_⟩
  have hh : G.point e.val.1=edgeCenter e-(1/2:ℝ) • carriedVector e := by
    dsimp [edgeCenter,RhombusCell.midpoint2,carriedVector]
    module
  rw [hh,hv]
  module

namespace PentagonSpokeLoops
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F}
    (K : PentagonSpokeLoops G F P)

def vertexCode (v : Fin n) : Fin 5→ℤ := fun i => (K.loop i).windingIndex (G.point v)
def rootCode (j : Fin 5) : Fin 5→ℤ := K.vertexCode (P.vertex j)

theorem spoke_bank_avoids_loop (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (j i : Fin 5) (sign : ℝ) (hsign : sign=1 ∨ sign= -1) :
    Disjoint ((K.spine j).bankRegion sign) (K.loop i).trace := by
  have hport (k : Fin 5) : P.dart k∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  exact (K.spine j).bankRegion_avoids_pair_loop ht (Finset.mem_filter.mp (hport j)).2.1
    (K.sink j) _ _
    (P.source_tracks_noncrossing ht hF _ _ (hport j) (hport i))
    (P.source_tracks_noncrossing ht hF _ _ (hport j) (hport (i+1)))
    F K.outer hF K.outer_unbounded (K.loop i) (K.support i) sign hsign

theorem carried_start_code (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (j : Fin 5) (e : OrientedEdge G) (he : edgeComponent e=edgeComponent (P.dart j)) :
    (carriedVector e=carriedVector (P.dart j) ∧ K.vertexCode e.val.1=K.rootCode j) ∨
      (carriedVector e= -carriedVector (P.dart j) ∧ K.vertexCode e.val.1=K.rootCode (j+1)) := by
  have hport : P.dart j∈G.faceSourcePorts F := by
    rw [← P.darts]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hs := (Finset.mem_filter.mp hport).2.1
  have hline : SameLine (carriedVector e) (carriedVector (P.dart j)) :=
    (component_sameLine e _ he).trans (component_sameLine (P.dart j) _ rfl).symm
  rcases hline with hv | hv
  · left
    refine ⟨hv,?_⟩
    have hE := (K.spine j).carried_start_mem_bank ht hs (K.sink j) e he (-1)
      (by simpa only [neg_neg,one_smul] using hv)
    have hS := (K.spine j).carried_start_mem_bank ht hs (K.sink j) (P.dart j) rfl (-1)
      (by simp only [neg_neg,one_smul])
    funext i
    exact (K.loop i).windingIndex_constant ((K.spine j).bankRegion_preconnected (-1))
      (K.spoke_bank_avoids_loop ht hF j i (-1) (Or.inr rfl)) hE hS
  · right
    refine ⟨hv,?_⟩
    have hE := (K.spine j).carried_start_mem_bank ht hs (K.sink j) e he 1
      (by simpa only [neg_one_smul] using hv)
    have hR := (K.spine j).carried_start_mem_bank ht hs (K.sink j) (reverseEdge (P.dart j))
      (reverse_component (P.dart j)).symm 1 (by rw [reverseEdge_vector,neg_one_smul])
    funext i
    exact (K.loop i).windingIndex_constant ((K.spine j).bankRegion_preconnected 1)
      (K.spoke_bank_avoids_loop ht hF j i 1 (Or.inl rfl)) hE hR

theorem nonspoke_edge_code_eq (ht : G.TriangleFree) (e : OrientedEdge G)
    (hne : ∀ i : Fin 5,edgeComponent e≠edgeComponent (P.dart i)) :
    K.vertexCode e.val.1=K.vertexCode e.val.2 := by
  funext i
  exact (K.support i).edge_endpoint_winding_eq ht e (hne i) (hne (i+1))

end PentagonSpokeLoops
end Swanepoel
