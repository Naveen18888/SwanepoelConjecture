module
public import Swanepoel.MaskedSpineBanks
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

namespace PlaneChain
def reverse {a b : Plane} : PlaneChain a b → PlaneChain b a
  | .nil a => .nil a
  | .cons a b c p => p.reverse.append (single b a)

theorem trace_reverse {a b : Plane} (p : PlaneChain a b) : p.reverse.trace=p.trace := by
  induction p with
  | nil => rfl
  | cons a b c p ih =>
    simp only [reverse,trace_append,trace_single,ih,trace]
    rw [segment_symm,union_comm]

theorem prefix_to_point {a b : Plane} (p : PlaneChain a b) {z : Plane} (hz : z∈p.trace) :
    ∃ q : PlaneChain a z, q.trace⊆p.trace := by
  induction p with
  | nil a =>
    have heq : z=a := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨.nil a,Set.Subset.rfl⟩
  | cons a b c p ih =>
    rcases hz with hs | ht
    · refine ⟨single a z,?_⟩
      rw [trace_single]
      exact ((convex_segment (𝕜 := ℝ) a b).segment_subset (left_mem_segment ℝ a b) hs).trans
        Set.subset_union_left
    · obtain ⟨q,hq⟩ := ih ht
      refine ⟨(single a b).append q,?_⟩
      rw [trace_append,trace_single]
      exact Set.union_subset Set.subset_union_left (hq.trans Set.subset_union_right)
end PlaneChain

theorem RhombusCell.center_mem_trackSpine {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (C : RhombusCell G) (cut : TrackComponent G)
    (hcut : edgeComponent C.edgeAB=cut ∨ edgeComponent C.edgeAD=cut) :
    C.center∈trackSpineTrace cut := by
  obtain ⟨e,f,hef,he,hmid,_⟩ := C.spineWitness ht cut hcut
  rw [← hmid]
  refine Or.inr ⟨e,f,he,hef,?_⟩
  rw [segment_eq_image]
  refine ⟨1/2,⟨by norm_num,by norm_num⟩,?_⟩
  dsimp [stepCenter,RhombusCell.midpoint2]
  module

theorem OrdinaryCutBanks.source_prefix_closing_chain {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (hcut : cut∈G.ordinaryTrackComponents) {e g : OrientedEdge G}
    (hext : ¬Bornology.IsBounded (G.sourceFace e).val)
    (C : RhombusCell G)
    (hAD : edgeComponent C.edgeAD=cut) :
    ∃ close : PlaneChain (edgeCenter g) (edgeCenter e),
      close.trace⊆(segment ℝ (edgeCenter g) C.center∪trackSpineTrace cut)∪
        ({edgeCenter e}∪B.outer.val) := by
  have hX := C.center_mem_trackSpine ht cut (Or.inr hAD)
  have hXp : C.center∈B.spine.toPlane.trace := by
    rw [B.spine.complete_trace ht B.source B.sink,B.component]
    exact hX
  obtain ⟨up,hup⟩ := B.spine.toPlane.prefix_to_point hXp
  have hup' : up.reverse.trace⊆trackSpineTrace cut := by
    rw [PlaneChain.trace_reverse]
    exact hup.trans (by rw [B.spine.complete_trace ht B.source B.sink,B.component])
  obtain ⟨outer,houter,hunique⟩ := G.exists_unique_outer_face
  have heF : G.sourceFace e=B.outer :=
    (hunique _ hext).trans (hunique _ B.outer_unbounded).symm
  have huF := ((G.ordinary_iff_sourceFace_eq_outer cut B.outer B.outer_unbounded).mp hcut)
    B.start B.source B.component
  have hep : G.sourceProbe e∈B.outer.val := by rw [← heF]; exact G.sourceProbe_mem_sourceFace e
  have huprobe : G.sourceProbe B.start∈B.outer.val := by
    rw [← huF]
    exact G.sourceProbe_mem_sourceFace B.start
  obtain ⟨ext,hexttrace⟩ := planeChain_of_segment_reachable huprobe
    (G.face_segment_reachable B.outer huprobe hep)
  let uc := PlaneChain.single (edgeCenter B.start) (G.sourceProbe B.start)
  let ec := PlaneChain.single (G.sourceProbe e) (edgeCenter e)
  let close := (PlaneChain.single (edgeCenter g) C.center).append
    (up.reverse.append (uc.append (ext.append ec)))
  have huConn := G.source_probe_connector_subset B.start
  have heConn := G.source_probe_connector_subset e
  rw [huF] at huConn
  rw [heF] at heConn
  have hsMid : edgeCenter B.start∈trackSpineTrace cut := Or.inl ⟨B.start,B.component,rfl⟩
  refine ⟨close,?_⟩
  simp only [close,PlaneChain.trace_append,PlaneChain.trace_single,uc,ec]
  apply Set.union_subset (fun _ hz => Or.inl (Or.inl hz))
  apply Set.union_subset (fun _ hz => Or.inl (Or.inr (hup' hz)))
  apply Set.union_subset
  · intro z hz
    rcases huConn hz with he | ho
    · exact Or.inl (Or.inr (he.symm ▸ hsMid))
    · exact Or.inr (Or.inr ho)
  · apply Set.union_subset (fun _ hz => Or.inr (Or.inr (hexttrace hz)))
    intro z hz
    rw [segment_symm] at hz
    exact Or.inr (heConn hz)

theorem MaskedSpineChain.exists_half_local_loop {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)
    (hcut : cut∈G.ordinaryTrackComponents) {e g h finish : OrientedEdge G}
    (p : MaskedSpineChain G cut e g) (he : SpineSource e)
    (hext : ¬Bornology.IsBounded (G.sourceFace e).val)
    (htop : ¬∃a,PositiveCellStep finish a) (hfull : Relation.ReflTransGen PositiveCellStep e finish)
    (hne : edgeComponent e≠cut) (C : RhombusCell G)
    (hG : g.val=(C.a,C.b)) (hH : h.val=(C.d,C.c)) (hpos : 0<cross2 C.u C.v)
    (hAD : edgeComponent C.edgeAD=cut) :
    ∃ loop : PlaneChain (edgeCenter e) (edgeCenter e),
      p.positive.toPlane.trace⊆loop.trace ∧
      loop.trace⊆(trackSpineTrace (edgeComponent e)∪trackSpineTrace cut)∪B.outer.val ∧
      ∀ sign : ℝ, sign=1 ∨ sign= -1 → Disjoint (p.positive.bankRegion sign) loop.trace := by
  obtain ⟨close,hclose⟩ := B.source_prefix_closing_chain ht hcut hext C hAD
  let loop := p.positive.toPlane.append close
  have hgc : edgeComponent g=edgeComponent e := (positive_path_component p.positive.reach).symm
  have hseg : segment ℝ (edgeCenter g) C.center⊆trackSpineTrace (edgeComponent e) := by
    have hgeq : g=C.edgeAB := Subtype.ext hG
    have hheq : h=C.edgeDC := Subtype.ext hH
    have hm : C.center=stepCenter g h := by rw [hgeq,hheq,C.stepCenter_eq]
    have hmid : C.center∈segment ℝ (edgeCenter g) (edgeCenter h) := by
      rw [hm,segment_eq_image]
      refine ⟨1/2,⟨by norm_num,by norm_num⟩,?_⟩
      dsimp [stepCenter,RhombusCell.midpoint2]
      module
    have hsub := (convex_segment (𝕜 := ℝ) (edgeCenter g) (edgeCenter h)).segment_subset
      (left_mem_segment ℝ _ _) hmid
    exact fun z hz => Or.inr ⟨g,h,hgc,⟨C,hG,hH,hpos⟩,hsub hz⟩
  have hsupport : loop.trace⊆(trackSpineTrace (edgeComponent e)∪trackSpineTrace cut)∪B.outer.val := by
    rw [PlaneChain.trace_append]
    apply Set.union_subset (fun _ hz => Or.inl (Or.inl (p.positive.trace_subset_track hz)))
    intro z hz
    rcases hclose hz with (hv | hu) | (he | ho)
    · exact Or.inl (Or.inl (hseg hv))
    · exact Or.inl (Or.inr hu)
    · exact Or.inl (Or.inl (Or.inl ⟨e,rfl,Set.mem_singleton_iff.mp he⟩))
    · exact Or.inr ho
  refine ⟨loop,?_,hsupport,?_⟩
  · change p.positive.toPlane.trace⊆(p.positive.toPlane.append close).trace
    rw [PlaneChain.trace_append]
    exact Set.subset_union_left
  · intro sign hsign
    exact p.bankRegion_avoids_two_spine_loop ht he htop hfull hne B.outer B.outer_unbounded
      loop hsupport sign hsign

end Swanepoel
