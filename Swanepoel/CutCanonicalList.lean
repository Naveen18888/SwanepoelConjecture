module
public import Swanepoel.CutBankConservation
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.admissibleOrdinaryCuts {n : ℕ} (G : PennyGraph n) : Finset (TrackComponent G) :=
  G.ordinaryTrackComponents.filter (fun c => ∃ d,ComponentCrosses c d)

def PennyGraph.chosenCutBanks {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (c : {c : TrackComponent G // c∈G.admissibleOrdinaryCuts}) : OrdinaryCutBanks G c.val :=
  Classical.choice (exists_ordinaryCutBanks ht c.val
    (Classical.choose (Finset.mem_filter.mp c.property).2)
    (Finset.mem_filter.mp c.property).1
    (Classical.choose_spec (Finset.mem_filter.mp c.property).2))

def PennyGraph.canonicalCutHalves {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : List HalfSystem :=
  G.admissibleOrdinaryCuts.attach.toList.flatMap (fun c =>
    [(G.chosenCutBanks ht c).canonicalHalfSystem ht false,
     (G.chosenCutBanks ht c).canonicalHalfSystem ht true])

theorem PennyGraph.mem_canonicalCutHalves {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (H : HalfSystem) : H∈G.canonicalCutHalves ht ↔
      ∃ c : {c : TrackComponent G // c∈G.admissibleOrdinaryCuts}, ∃ side : Bool,
        H=(G.chosenCutBanks ht c).canonicalHalfSystem ht side := by
  simp only [PennyGraph.canonicalCutHalves,List.mem_flatMap,Finset.mem_toList,
    Finset.mem_attach,true_and,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨c,h | h⟩
    · exact ⟨c,false,h⟩
    · exact ⟨c,true,h⟩
  · rintro ⟨c,side,h⟩
    cases side
    · exact ⟨c,Or.inl h⟩
    · exact ⟨c,Or.inr h⟩

theorem PennyGraph.canonicalCutHalves_realized {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (hc : G.graph.Connected) (H : HalfSystem) (hH : H∈G.canonicalCutHalves ht) :
    ∃ cut : TrackComponent G,∃ B : OrdinaryCutBanks G cut,
      cut∈G.ordinaryTrackComponents ∧ ∃ side : Bool,Nonempty (H.BankRealization B ht side) := by
  obtain ⟨c,side,rfl⟩ := (G.mem_canonicalCutHalves ht H).mp hH
  have hcut := (Finset.mem_filter.mp c.property).1
  exact ⟨c.val,G.chosenCutBanks ht c,hcut,side,
    ⟨(G.chosenCutBanks ht c).canonicalHalfBankRealization ht hc hcut side⟩⟩

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bankVertices_partition :
    Disjoint (B.bankVertices false) (B.bankVertices true) ∧
      B.bankVertices false∪B.bankVertices true=Finset.univ := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    have h := ((B.mem_bankVertices false v).mp hv).symm.trans ((B.mem_bankVertices true v).mp hw)
    cases h
  · ext v
    cases h : B.vertexBankCode v <;> simp [bankVertices,h]

theorem half_vertex_count_sum :
    (B.bankVertices false).card+(B.bankVertices true).card=n := by
  rw [← Finset.card_union_of_disjoint B.bankVertices_partition.1,
    B.bankVertices_partition.2,Finset.card_univ,Fintype.card_fin]

theorem half_vertex_count_lt (ht : G.TriangleFree) (side : Bool) :
    (B.bankVertices side).card<n := by
  have h := B.half_vertex_count_sum
  have hl := (B.bankVertices_nonempty ht false).card_pos
  have hr := (B.bankVertices_nonempty ht true).card_pos
  cases side <;> omega

end OrdinaryCutBanks
end Swanepoel
