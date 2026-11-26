module
public import Swanepoel.SectorConstruction
public import Swanepoel.JoinClosedFamilies
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace SectorPortData
variable {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {u v : TrackComponent G} {Label : Type*} (D : SectorPortData G ht u v Label)

def selectedFamily (Y : Finset (PlaneFace G)) : Finset (OrientedEdge G) :=
  D.selected.filter (fun e => G.sourceFace e∈Y)

theorem selectedFamily_fiber (Y : Finset (PlaneFace G)) (F : PlaneFace G) (hF : F∈Y) :
    (D.selectedFamily Y).filter (fun e => G.sourceFace e=F)=
      D.selected.filter (fun e => G.sourceFace e=F) := by
  ext e
  simp only [selectedFamily,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,h.2 ▸ hF⟩,h.2⟩

theorem selectedFamily_card_lower (Y : Finset (PlaneFace G))
    (hY : Y⊆G.defectPlaneFaces ht)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b) :
    2*Y.card≤(D.selectedFamily Y).card := by
  have hcard := Finset.card_eq_sum_card_fiberwise (f := G.sourceFace)
    (s := D.selectedFamily Y) (t := Y) (fun e he => (Finset.mem_filter.mp he).2)
  calc
    _ = ∑ _∈Y, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ F∈Y, ((D.selectedFamily Y).filter (fun e => G.sourceFace e=F)).card := by
      apply Finset.sum_le_sum
      intro F hF
      rw [D.selectedFamily_fiber Y F hF,D.selected_face_fiber F (hY hF)]
      exact G.defect_two_semicircle_ports ht F (hY hF) hdegree _ (D.direction_ne_zero _)
    _ = _ := hcard.symm

include D

theorem family_anchor_crossing_count (Y : Finset (PlaneFace G))
    (hY : Y⊆G.defectPlaneFaces ht)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (huv : ComponentCrosses u v) :
    ((G.familyTrackComponents Y).filter (ComponentCrosses u)).card+
      ((G.familyTrackComponents Y).filter (ComponentCrosses v)).card+
      2*Y.card≤(G.familyTrackComponents Y).card := by
  let A := G.familyTrackComponents Y
  let U := A.filter (ComponentCrosses u)
  let V := A.filter (ComponentCrosses v)
  let S := D.selectedFamily Y
  let P := S.image edgeComponent
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro c hcU hcV
    exact componentGraph_noTriple G ht u v c huv (Finset.mem_filter.mp hcV).2
      ((componentGraph G ht).adj_symm (Finset.mem_filter.mp hcU).2)
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.mpr
    intro c hcU hcP
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hcP
    exact (D.selected_missing (Finset.mem_filter.mp he).1).1 (Finset.mem_filter.mp hcU).2
  have hVP : Disjoint V P := by
    apply Finset.disjoint_left.mpr
    intro c hcV hcP
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hcP
    exact (D.selected_missing (Finset.mem_filter.mp he).1).2 (Finset.mem_filter.mp hcV).2
  have hPsub : P⊆A := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,D.selected_source he'.1,he'.2⟩,rfl⟩
  have hinj : Set.InjOn edgeComponent (S : Set (OrientedEdge G)) :=
    D.selected_component_injective.mono (Finset.filter_subset _ _)
  have hPcard : P.card=S.card := Finset.card_image_of_injOn hinj
  have hsub : (U∪V)∪P⊆A := Finset.union_subset
    (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) hPsub
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hUP,hVP⟩),
    Finset.card_union_of_disjoint hUV,hPcard] at hcount
  have hlower := D.selectedFamily_card_lower Y hY hdegree
  change 2*Y.card≤S.card at hlower
  change U.card+V.card+2*Y.card≤A.card
  omega

end SectorPortData

theorem PennyGraph.half_anchor_bound_original_ordinary {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (cut nonAnchor : TrackComponent G) (hcut : cut∈G.ordinaryTrackComponents)
    (hnonAnchor : nonAnchor∈G.ordinaryTrackComponents) (hcross : ComponentCrosses cut nonAnchor)
    (Y : Finset (PlaneFace G)) (hY : Y⊆G.defectPlaneFaces ht) :
    (((G.familyTrackComponents Y).filter (ComponentCrosses nonAnchor)).card : ℤ)≤
      (G.familyTrackComponents Y).card-
        ((G.familyTrackComponents Y).filter (ComponentCrosses cut)).card-2*Y.card := by
  obtain ⟨D⟩ := actual_sector_port_data ht cut nonAnchor hcut hnonAnchor hcross
  have hnat := D.family_anchor_crossing_count Y hY hdegree hcross
  have hi : (((G.familyTrackComponents Y).filter (ComponentCrosses cut)).card : ℤ)+
      ((G.familyTrackComponents Y).filter (ComponentCrosses nonAnchor)).card+
      2*Y.card≤(G.familyTrackComponents Y).card := by exact_mod_cast hnat
  omega

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def bankDefectFamily (ht : G.TriangleFree) (side : Bool) : Finset (PlaneFace G) :=
  (G.defectPlaneFaces ht).filter (fun F => B.bankCode F=side)

def bankAnchorTracks (ht : G.TriangleFree) (side : Bool) : Finset (TrackComponent G) :=
  G.familyTrackComponents (B.bankDefectFamily ht side)

def bankMeetingAnchors (ht : G.TriangleFree) (side : Bool) : Finset (TrackComponent G) :=
  (B.bankAnchorTracks ht side).filter (ComponentCrosses cut)

def bankK (ht : G.TriangleFree) (side : Bool) : ℤ :=
  (B.bankAnchorTracks ht side).card-2*(B.bankDefectFamily ht side).card

theorem original_ordinary_nonAnchor_bound (ht : G.TriangleFree)
    (hdegree : ∀ a b, G.graph.Adj a b → ∃ c, G.graph.Adj a c ∧ c≠b)
    (hcut : cut∈G.ordinaryTrackComponents) (v : TrackComponent G)
    (hv : v∈G.ordinaryTrackComponents) (hcross : ComponentCrosses cut v) (side : Bool) :
    (((B.bankAnchorTracks ht side).filter (ComponentCrosses v)).card : ℤ)≤
      B.bankK ht side-(B.bankMeetingAnchors ht side).card := by
  have hh := G.half_anchor_bound_original_ordinary ht hdegree cut v hcut hv hcross
    (B.bankDefectFamily ht side) (Finset.filter_subset _ _)
  change (((B.bankAnchorTracks ht side).filter (ComponentCrosses v)).card : ℤ)≤
    (B.bankAnchorTracks ht side).card-(B.bankMeetingAnchors ht side).card-
      2*(B.bankDefectFamily ht side).card at hh
  unfold bankK
  omega

end OrdinaryCutBanks

end Swanepoel
