module
public import Swanepoel.BoundarySpokeClosing
public import Swanepoel.LoopConjugation
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

theorem physicalEdge_reverse {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    physicalEdge (reverseEdge e)=physicalEdge e := by
  apply Subtype.ext
  by_cases h : e.val.1<e.val.2
  · have hn : ¬e.val.2<e.val.1 := not_lt_of_ge h.le
    simp [physicalEdge,reverseEdge,h,hn]
  · have hp : e.val.2<e.val.1 := lt_of_le_of_ne (le_of_not_gt h) e.property.ne.symm
    simp [physicalEdge,reverseEdge,h,hp]

theorem PennyGraph.source_probes_symmetric {n : ℕ} (G : PennyGraph n) (e : OrientedEdge G) :
    ∃ δ : ℝ,0<δ ∧ G.sourceProbe e=edgeCenter e-δ • quarterTurn (carriedVector e) ∧
      G.sourceProbe (reverseEdge e)=edgeCenter e+δ • quarterTurn (carriedVector e) := by
  let δ := G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2)
  have hdraw : G.sourceProbeDrawing (reverseEdge e)=G.sourceProbeDrawing e := by
    unfold sourceProbeDrawing
    rw [physicalEdge_reverse]
  refine ⟨δ,G.sourceProbe_offset_pos e,?_,?_⟩
  · rw [G.sourceProbe_eq_normal_offset,← edgeCenter_eq_midpoint]
    dsimp only [sourceNormal,δ]
    module
  · rw [G.sourceProbe_eq_normal_offset,hdraw,physicalEdge_reverse,← edgeCenter_eq_midpoint,
      edgeCenter_reverse]
    simp only [sourceNormal,reverseEdge_vector,quarterTurn_neg,neg_neg]
    rfl

theorem PennyGraph.boundary_nil_spoke_pair_banks {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (F : PlaneFace G) (hFY : F∈Y)
    (hports : ∀ s∈G.faceSourcePorts F,edgeComponent s∈G.familyBoundaryTrackComponents Y)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (e f : OrientedEdge G) (he : e∈G.faceSourcePorts F) (hf : f∈G.faceSourcePorts F)
    (hne : edgeComponent e≠edgeComponent f) (hmiss : ¬ComponentCrosses (edgeComponent e) (edgeComponent f))
    (htop : ¬∃g,PositiveCellStep e g) (heOuter : G.sourceFace (reverseEdge e)=outer) :
    ∃ loop : PlaneChain (edgeCenter e) (edgeCenter e),
      G.SpokePairSupport (edgeComponent e) (edgeComponent f) F outer loop ∧
      trackSpineTrace (edgeComponent e)⊆loop.trace ∧ trackSpineTrace (edgeComponent f)⊆loop.trace ∧
      (∀ sign : ℝ,sign=1 ∨ sign= -1 →
        Disjoint ((PositiveSpineChain.nil e).bankRegion sign) loop.trace) ∧
      (PositiveSpineChain.nil e).bankLabel loop (-1)=(PositiveSpineChain.nil e).bankLabel loop 1+1 := by
  obtain ⟨δ,hδ,ha,hb⟩ := G.source_probes_symmetric e
  let m := edgeCenter e
  let v := carriedVector e
  let a := m-δ • quarterTurn v
  let b := m+δ • quarterTurn v
  have ha' : G.sourceProbe e=a := ha
  have hb' : G.sourceProbe (reverseEdge e)=b := hb
  have heF := (Finset.mem_filter.mp he).2.2
  have hfF := (Finset.mem_filter.mp hf).2.2
  have hs : SpineSource e := (Finset.mem_filter.mp he).2.1
  obtain ⟨u,huTop,hfu,huF⟩ := G.boundary_port_complete_spine_to_outer ht hY F hFY hports outer houter f hf
  obtain ⟨q⟩ := PositiveSpineChain.exists_of_reach hfu
  have hq := q.complete_trace ht (Finset.mem_filter.mp hf).2.1 huTop
  have hmf : edgeCenter f∈trackSpineTrace (edgeComponent f) := Or.inl ⟨f,rfl,rfl⟩
  have hmu : edgeCenter u∈trackSpineTrace (edgeComponent f) :=
    Or.inl ⟨u,(positive_path_component hfu).symm,rfl⟩
  have hfp : G.sourceProbe f∈F.val := by rw [← hfF]; exact G.sourceProbe_mem_sourceFace f
  have hep : G.sourceProbe e∈F.val := by rw [← heF]; exact G.sourceProbe_mem_sourceFace e
  have hrp : G.sourceProbe (reverseEdge e)∈outer.val := by
    rw [← heOuter]; exact G.sourceProbe_mem_sourceFace _
  have hup : G.sourceProbe (reverseEdge u)∈outer.val := by
    rw [← huF]; exact G.sourceProbe_mem_sourceFace _
  obtain ⟨inside,hinside⟩ := planeChain_of_segment_reachable hfp (G.face_segment_reachable F hfp hep)
  obtain ⟨outside,houtside⟩ := planeChain_of_segment_reachable hrp (G.face_segment_reachable outer hrp hup)
  let restRaw := outside.append ((PlaneChain.single (G.sourceProbe (reverseEdge u)) (edgeCenter u)).append
    (q.toPlane.reverse.append ((PlaneChain.single (edgeCenter f) (G.sourceProbe f)).append inside)))
  let S := (trackSpineTrace (edgeComponent f)∪F.val)∪outer.val
  have hcu : segment ℝ (G.sourceProbe (reverseEdge u)) (edgeCenter u)⊆S := by
    have hh := G.source_probe_connector_subset (reverseEdge u)
    rw [edgeCenter_reverse,huF] at hh
    rw [segment_symm]
    intro z hz
    rcases hh hz with hz | hz
    · exact Or.inl (Or.inl ((Set.mem_singleton_iff.mp hz).symm ▸ hmu))
    · exact Or.inr hz
  have hcf : segment ℝ (edgeCenter f) (G.sourceProbe f)⊆S := by
    have hh := G.source_probe_connector_subset f
    rw [hfF] at hh
    intro z hz
    rcases hh hz with hz | hz
    · exact Or.inl (Or.inl ((Set.mem_singleton_iff.mp hz).symm ▸ hmf))
    · exact Or.inl (Or.inr hz)
  have hrestRaw : restRaw.trace⊆S := by
    simp only [restRaw,PlaneChain.trace_append,PlaneChain.trace_single,PlaneChain.trace_reverse,hq]
    exact Set.union_subset (fun _ hz => Or.inr (houtside hz)) (Set.union_subset hcu
      (Set.union_subset (fun _ hz => Or.inl (Or.inl hz))
        (Set.union_subset hcf (fun _ hz => Or.inl (Or.inr (hinside hz))))))
  let rest := restRaw.changeEndpoints hb' ha'
  have hrest : rest.trace⊆S := by rw [PlaneChain.trace_changeEndpoints]; exact hrestRaw
  have hfull : trackSpineTrace (edgeComponent f)⊆rest.trace := by
    rw [PlaneChain.trace_changeEndpoints]
    simp only [restRaw,PlaneChain.trace_append,PlaneChain.trace_single,PlaneChain.trace_reverse,hq]
    exact fun _ hz => Or.inr (Or.inr (Or.inl hz))
  have hnot : m∉S := by
    rintro ((hz | hz) | hz)
    · have hem : m∈G.edgeTrace e.val.1 e.val.2 :=
        ⟨1/2,⟨by norm_num,by norm_num⟩,(edgeCenter_eq_midpoint e).symm⟩
      exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht e _ hne) hem hz
    · exact G.face_subset_complement F hz (G.edgeCenter_mem_drawing e)
    · exact G.face_subset_complement outer hz (G.edgeCenter_mem_drawing e)
  let L := (PlaneChain.single a b).append rest
  let loop := L.conjugate m
  have hconnF : segment ℝ m a⊆{m}∪F.val := by
    have hh := G.source_probe_connector_subset e
    rwa [ha',heF] at hh
  have hconnO : segment ℝ m b⊆{m}∪outer.val := by
    have hh := G.source_probe_connector_subset (reverseEdge e)
    rwa [edgeCenter_reverse,hb',heOuter] at hh
  have hm : m∈trackSpineTrace (edgeComponent e) := Or.inl ⟨e,rfl,rfl⟩
  have hconnFS : segment ℝ m a⊆((trackSpineTrace (edgeComponent e)∪
      trackSpineTrace (edgeComponent f))∪F.val)∪outer.val := by
    intro z hz
    rcases hconnF hz with hz | hz
    · exact Or.inl (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hz).symm ▸ hm)))
    · exact Or.inl (Or.inr hz)
  have hconnOS : segment ℝ m b⊆((trackSpineTrace (edgeComponent e)∪
      trackSpineTrace (edgeComponent f))∪F.val)∪outer.val := by
    intro z hz
    rcases hconnO hz with hz | hz
    · exact Or.inl (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hz).symm ▸ hm)))
    · exact Or.inr hz
  have hsupport : G.SpokePairSupport (edgeComponent e) (edgeComponent f) F outer loop := by
    dsimp only [PennyGraph.SpokePairSupport,loop]
    rw [PlaneChain.trace_conjugate,PlaneChain.trace_append,PlaneChain.trace_single]
    refine Set.union_subset hconnFS (Set.union_subset ?_ ?_)
    · exact (symmetric_segment_subset_halves m (δ • quarterTurn v)).trans
        (Set.union_subset hconnFS hconnOS)
    · intro z hz
      rcases hrest hz with (hz | hz) | hz
      · exact Or.inl (Or.inl (Or.inr hz))
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
  have hdis := (PositiveSpineChain.nil e).bankRegion_avoids_spoke_pair_loop ht hs htop
    _ hne hmiss F outer (hY.subset_defects hFY) houter loop hsupport
  have hmLoop : m∈loop.trace := by
    rw [PlaneChain.trace_conjugate]
    exact Or.inl (left_mem_segment ℝ m a)
  have hown : trackSpineTrace (edgeComponent e)⊆loop.trace := by
    rw [← (PositiveSpineChain.nil e).complete_trace ht hs htop]
    exact Set.singleton_subset_iff.mpr hmLoop
  have hother : trackSpineTrace (edgeComponent f)⊆loop.trace := by
    dsimp only [loop,L]
    rw [PlaneChain.trace_conjugate,PlaneChain.trace_append]
    exact hfull.trans (Set.subset_union_right.trans Set.subset_union_right)
  refine ⟨loop,hsupport,hown,hother,hdis,?_⟩
  obtain ⟨ε,hε,hjump⟩ := symmetric_normal_loop_winding_jump m v (carriedVector_norm e) δ hδ rest
    (fun hz => hnot (hrest hz))
  let r := min ε (1/(4*δ))/2
  have hr : 0<r := by dsimp [r]; positivity
  have hre : r<ε := by have := min_le_left ε (1/(4*δ)); dsimp [r]; linarith
  have hrb : r<1/(4*δ) := by
    have := min_le_right ε (1/(4*δ))
    have hbpos : 0<1/(4*δ) := by positivity
    dsimp [r]
    linarith
  have hβ : 0<2*δ*r := by positivity
  have hbound : 2*δ*r≤1/2 := by
    have hh := mul_lt_mul_of_pos_right hrb (by positivity : 0<4*δ)
    rw [one_div_mul_cancel (by positivity : 4*δ≠0)] at hh
    nlinarith only [hh]
  have hp : m+(2*δ*r) • v∈(PositiveSpineChain.nil e).bankRegion 1 := by
    exact ⟨m,Set.mem_singleton m,2*δ*r,⟨hβ,hbound⟩,by simp [v]⟩
  have hn : m+(-(2*δ*r)) • v∈(PositiveSpineChain.nil e).bankRegion (-1) := by
    exact ⟨m,Set.mem_singleton m,2*δ*r,⟨hβ,hbound⟩,by simp [v]⟩
  have hj := hjump r hr hre
  change loop.windingIndex _=loop.windingIndex _+1 at hj
  rw [(PositiveSpineChain.nil e).bankLabel_constant_of_disjoint loop (-1) (hdis (-1) (Or.inr rfl)) hn,
    (PositiveSpineChain.nil e).bankLabel_constant_of_disjoint loop 1 (hdis 1 (Or.inl rfl)) hp] at hj
  exact hj

end Swanepoel
