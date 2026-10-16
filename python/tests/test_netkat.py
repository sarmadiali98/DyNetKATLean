"""Golden tests for NetKAT denotational semantics.

These tests verify the Python mirror of the NetKAT semantics
to cross-check the Lean formalization.
"""
import pytest


# ---- Packet model ----

class Packet:
    """A packet maps field names to values."""
    
    def __init__(self, fields=None):
        self.fields = dict(fields or {})
    
    def get(self, field):
        return self.fields.get(field, FieldValue.V0)
    
    def update(self, field, value):
        new_fields = dict(self.fields)
        new_fields[field] = value
        return Packet(new_fields)
    
    def __eq__(self, other):
        if not isinstance(other, Packet):
            return False
        # Two packets are equal if they agree on all fields
        fields = set(self.fields.keys()) | set(other.fields.keys())
        return all(self.get(f) == other.get(f) for f in fields)
    
    def __hash__(self):
        return hash(tuple(sorted(self.fields.items())))


class FieldValue:
    V0 = 0
    V1 = 1
    V8 = 8
    V9 = 9


class FieldName:
    TP_SRC = "tp_src"
    TP_DST = "tp_dst"
    SW_ID = "sw_id"
    PORT = "port"


# ---- Complete tests ----

class CompleteTest:
    """A complete test is a set of field=value constraints."""
    
    def __init__(self, constraints=None):
        self.constraints = set(constraints or [])
    
    def holds(self, packet):
        """Test holds iff all constraints match."""
        return all(packet.get(f) == v for f, v in self.constraints)


# ---- NetKAT semantics ----

def semantics_drop(packet_in):
    """⟦0⟧ = ∅: drop produces no output."""
    return set()

def semantics_id(packet_in):
    """⟦1⟧ = {(σ,σ)}: identity preserves packet."""
    return {packet_in}

def semantics_test(test, packet_in):
    """⟦f=v⟧ = {(σ,σ) | σ(f) = v}: test preserves packet iff field matches."""
    if test.holds(packet_in):
        return {packet_in}
    return set()

def semantics_assign(packet_out, packet_in):
    """⟦π⟧ = {(σ, π(σ))}: assignment maps to output packet."""
    return {packet_out}

def semantics_union(n1_sem, n2_sem, packet_in):
    """⟦N₁+N₂⟧ = ⟦N₁⟧ ∪ ⟦N₂⟧."""
    return n1_sem(packet_in) | n2_sem(packet_in)

def semantics_seq(n1_sem, n2_sem, packet_in):
    """⟦N₁;N₂⟧ = ⟦N₁⟧ ∘ ⟦N₂⟧: relational composition."""
    intermediate = n1_sem(packet_in)
    result = set()
    for mid in intermediate:
        result |= n2_sem(mid)
    return result

def semantics_star(body_sem, packet_in, max_iterations=10):
    """⟦N*⟧ = ⋃ₖ ⟦N⟧ᵏ: reflexive-transitive closure.
    
    On finite domains this terminates. We bound the iteration
    to prevent infinite loops.
    """
    # Start with identity (reflexive: (σ,σ) ∈ ⟦N*⟧)
    results = {packet_in}
    new = {packet_in}
    for _ in range(max_iterations):
        next_new = set()
        for p in new:
            next_new |= body_sem(p)
        if next_new <= results:
            break
        results |= next_new
        new = next_new
    return results


# ---- Tests ----

class TestPacketModel:
    """Tests for the packet model."""
    
    def test_packet_get(self):
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        assert p.get(FieldName.TP_SRC) == FieldValue.V8
    
    def test_packet_update(self):
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        p2 = p.update(FieldName.TP_SRC, FieldValue.V9)
        assert p2.get(FieldName.TP_SRC) == FieldValue.V9
    
    def test_packet_update_different_field(self):
        p = Packet({FieldName.TP_SRC: FieldValue.V8, FieldName.TP_DST: FieldValue.V0})
        p2 = p.update(FieldName.TP_DST, FieldValue.V9)
        assert p2.get(FieldName.TP_SRC) == FieldValue.V8
        assert p2.get(FieldName.TP_DST) == FieldValue.V9


class TestCompleteTests:
    """Tests for complete tests."""
    
    def test_empty_test_holds(self):
        test = CompleteTest()
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        assert test.holds(p)
    
    def test_single_test_holds(self):
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        assert test.holds(p)
    
    def test_single_test_fails(self):
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p = Packet({FieldName.TP_SRC: FieldValue.V9})
        assert not test.holds(p)


class TestNetKATSemantics:
    """Tests for NetKAT denotational semantics."""
    
    def test_drop_empty(self):
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        result = semantics_drop(p)
        assert result == set()
    
    def test_id_diagonal(self):
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        result = semantics_id(p)
        assert result == {p}
    
    def test_test_holds(self):
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        result = semantics_test(test, p)
        assert result == {p}
    
    def test_test_fails(self):
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p = Packet({FieldName.TP_SRC: FieldValue.V9})
        result = semantics_test(test, p)
        assert result == set()
    
    def test_union(self):
        test1 = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        test2 = CompleteTest([(FieldName.TP_SRC, FieldValue.V9)])
        p8 = Packet({FieldName.TP_SRC: FieldValue.V8})
        p9 = Packet({FieldName.TP_SRC: FieldValue.V9})
        
        result = semantics_union(
            lambda p: semantics_test(test1, p),
            lambda p: semantics_test(test2, p),
            p8
        )
        assert result == {p8}
        
        result = semantics_union(
            lambda p: semantics_test(test1, p),
            lambda p: semantics_test(test2, p),
            p9
        )
        assert result == {p9}
    
    def test_seq(self):
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p8 = Packet({FieldName.TP_SRC: FieldValue.V8})
        p9 = Packet({FieldName.TP_SRC: FieldValue.V9})
        
        # (tpSrc=8 ; id) on p8 should give {p8}
        result = semantics_seq(
            lambda p: semantics_test(test, p),
            semantics_id,
            p8
        )
        assert result == {p8}
        
        # (tpSrc=8 ; id) on p9 should give {} (test fails)
        result = semantics_seq(
            lambda p: semantics_test(test, p),
            semantics_id,
            p9
        )
        assert result == set()
    
    def test_star_reflexive(self):
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        # N* should always contain (σ, σ) - reflexive
        result = semantics_star(semantics_id, p)
        assert p in result
    
    def test_star_empty_body(self):
        # 0* = id (since 0 produces nothing, star is just identity)
        p = Packet({FieldName.TP_SRC: FieldValue.V8})
        result = semantics_star(semantics_drop, p)
        assert result == {p}


class TestNetKATExamples:
    """Tests using concrete NetKAT examples from the paper."""
    
    def test_tpSrc8_drop(self):
        """(tp_src = 8);drop evaluates to empty for packets with tp_src = 8."""
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p8 = Packet({FieldName.TP_SRC: FieldValue.V8})
        
        result = semantics_seq(
            lambda p: semantics_test(test, p),
            semantics_drop,
            p8
        )
        assert result == set()
    
    def test_tpSrc8_drop_fails_on_9(self):
        """(tp_src = 8);drop on a packet with tp_src = 9 produces empty."""
        test = CompleteTest([(FieldName.TP_SRC, FieldValue.V8)])
        p9 = Packet({FieldName.TP_SRC: FieldValue.V9})
        
        result = semantics_seq(
            lambda p: semantics_test(test, p),
            semantics_drop,
            p9
        )
        assert result == set()
