# DyNetiKAT Reference Tool Audit

**Audit type:** Research and documentation only. No code modifications.
**Repository audited:** `/Users/ali/Desktop/DyNetKAT` (read-only reference)
**Official repository:** [University of Twente GitLab](https://gitlab.utwente.nl/fmt/dynetikat). The historical audit below used the matching GitHub copy.
**Examined Git revision:** `1c6bd422377853378c7516a7875009fcfb5ba881` (HEAD of `master` as of 2026-10-17)
**Release tag:** `v1.1` (points to the same commit `1c6bd42`)
**Commit date:** 2021-10-09
**Auditor:** DyNetKAT-Lean planning task P1

---

## 0. Summary

| Aspect | Finding |
|---|---|
| Tool name | DyNetiKAT (note the internal "i" — `DyNetiKAT`, not `DyNetKAT`) |
| License | MIT (University of Konstanz, 2021) |
| Implementation language | Python 3 (glue/orchestration) + Maude (rewriting backend) |
| NetKAT backend | External: `netkat-idd` (`katbv`) or `netkat-automata` — **not bundled in this repo** |
| Paper bundled | `paper.pdf` (conference-style manuscript bundled by the tool) |
| Architecture | Two-stage pipeline: (1) preprocessing/equational rewriting via Maude, (2) property checking via NetKAT decision procedure |

The prototype performs analysis by invoking Maude and a NetKAT decision
procedure. The [current roadmap](../PLAN.md) specifies the Lean trust
boundary and the use of external tools for reference runs or checked
certificates. See the [current feature parity matrix](#v11-feature-parity)
for the re-audited revision and workflow.

---

## 1. Repository Structure (confirmed)

```
DyNetiKAT/
├── README.md                 # User-facing documentation
├── LICENSE                   # MIT
├── dnk.py                    # CLI entry point
├── install.sh                # Dependency installation script
├── run_test.sh               # Example: run stateful firewall test
├── run_fattree.sh            # Example: run FatTree experiments
├── paper.pdf                 # Conference-style manuscript (bundled)
├── src/
│   ├── maude/
│   │   ├── dnk.maude         # Main Maude module: DyNetKAT axioms + head/tail operators
│   │   └── preprocess.maude  # Preprocessing Maude module: parse annotations
│   └── python/
│       ├── dynetkat.py       # Core analysis class (DyNetKAT)
│       ├── preprocess.py     # Preprocessing class (Maude + NetKAT normalization)
│       ├── maude_parser.py   # Maude subprocess wrapper
│       ├── netkat_parser.py  # NetKAT decision procedure subprocess wrapper
│       └── util.py           # File/process utilities
└── benchmarks/
    ├── stateful_firewall.json
    ├── distributed_controller.py
    ├── distributed_controller_independent.json
    ├── distributed_controller_synchronized.json
    ├── fattree.py
    └── util.py
```

---

## 2. Command-Line Invocation

**Confirmed (from `dnk.py:20-32` and README.md):**

```
python3 dnk.py <path_to_maude> <path_to_netkat_tool> <input_file> [options]
```

### Parameters

Positional arguments (required):

| Argument | Source | Description |
|---|---|---|
| `<path_to_maude>` | `dnk.py:38-40` | Path to Maude executable (must be executable, `is_exe` checked) |
| `<path_to_netkat_tool>` | `dnk.py:42-44` | Path to NetKAT decision procedure executable (must be executable) |
| `<input_file>` | `dnk.py:46-48` | Path to `.json` input file (`is_json` checked: must end in `.json`) |

Options (optional):

| Flag | Default | Source | Description |
|---|---|---|---|
| `-t, --threads NUM_THREADS` | Number of available cores | `dnk.py:24-25` | Number of worker processes for parallel property checking |
| `-p, --preprocessed` | `False` | `dnk.py:26-27` | Skip preprocessing if input is already preprocessed |
| `-v, --netkat-version=VERSION` | `netkat-idd` | `dnk.py:28-29` | NetKAT tool version: `netkat-idd` or `netkat-automata` |
| `-s, --time-stats` | `False` | `dnk.py:30-31` | Print timing breakdown (total, preprocessing, NetKAT decision time) |

### NetKAT tool path expectations

**Confirmed (from README.md:36-37, `netkat_parser.py:42-56`):**

- `netkat-idd`: expects path to `katbv` binary (e.g., `netkat/_build/install/default/bin/katbv`).
  Invoked as: `katbv equiv <file1> <file2>`
- `netkat-automata`: expects `Decide_Repl.native` binary.
  Invoked as: `Decide_Repl.native "(term1) == (term2)"`

### Dependencies (from `install.sh:1-22`)

**Confirmed:** The tool requires:
1. Python 3.7+ with `numpy` and `networkx`
2. Maude >= 3.0
3. NetKAT tool (`netkat-idd` via opam, or `netkat-automata`)

**Note:** The NetKAT tool is cloned from `https://github.com/netkat-lang/netkat/` — it is
**not** bundled in the DyNetiKAT repository. It is an external dependency.

---

## 3. Input Format (JSON Schema)

**Confirmed (from README.md:85-131, `stateful_firewall.json`, `distributed_controller_independent.json`):**

The input is a `.json` file containing these keys:

### Required fields

| Field | Type | Source | Description |
|---|---|---|---|
| `module_name` | string | `dnk.py:54`, README | Name used for output files and Maude module |
| `recursive_variables` | dict (name -> string) | `dnk.py:52`, README | Recursive variable definitions. Values are DyNetKAT expressions. NetKAT sub-terms are enclosed in double quotes. |
| `program` | string | README | The main DyNetKAT program expression |
| `channels` | list of strings | README | Channel names appearing in the program |
| `in_packets` | dict (key -> string) | README | Ingress packet predicates. Keys must match `out_packets` keys. |
| `out_packets` | dict (key -> string) | README | Egress packet predicates. Keys must match `in_packets` keys. |
| `properties` | dict (key -> list of lists) | README | Per-packet properties to verify |

### Property format

Each property is a 4-element list:

```json
[<type>, <property_expression>, <expected_result>, <max_unfoldings>]
```

| Element | Type | Values | Source | Description |
|---|---|---|---|---|
| `type` | string | `"r"` (reachability), `"w"` (waypointing) | `dynetkat.py:72-86`, README:77 | Property type |
| `expression` | string | `head(@Program)`, `tail(@Program, {rcfg(...)})`, etc. | README:78, 82 | Property formula using `head`/`tail` operators |
| `expected` | string | `"!0"` (reachable), `"=0"` (unreachable), or a waypoint predicate | README:79, 82, 84 | Expected result |
| `unfoldings` | int | any positive integer (e.g., 2, 3, 5, 100) | README:80 | Max unfoldings for `pi_n` projection |

**Confirmed from examples:**
- Reachability: `["r", "head(@Program)", "!0", 100]` — checks if egress is reachable from ingress
- Reachability (after sync events): `["r", "(head(tail(@Program, {rcfg(...)})))", "!0", 100]`
- Waypointing: `["w", "(head({}))", "sw = 1", 100]` — checks if packets pass through waypoint `sw = 1`

---

## 4. Supported Language Constructs

### 4.1 NetKAT syntax (from README.md:53-61)

**Confirmed (README.md:53-61, paper text p. 167-168):**

| Paper notation | Tool encoding | Source | Description |
|---|---|---|---|
| `0` (drop) | `zero` | README:54 | Predicate that drops a packet |
| `1` (identity) | `one` | README:55 | Predicate that passes packet unchanged |
| `f = n` | `f = n` | README:56 | Field equality test |
| `f <- n` | `f <- n` | README:58 | Field assignment |
| `Pr + Pb` | `arg1 + arg2` | README:59 | Union (disjunction) |
| `Pr . Pb` | `arg1 . arg2` | README:60 | Sequential composition (conjunction) |
| `Pr *` | `arg1 *` | README:61 | Kleene star (iteration) |
| `~Pr` | `~ arg1` | README:57 | Negation |

### 4.2 DyNetKAT syntax (from README.md:42-50)

**Confirmed (README.md:42-50, paper text p. 300, Maude `dnk.maude:26-36`):**

| Paper notation | Tool encoding | Source | Description |
|---|---|---|---|
| `bot` (deadlock/bottom) | `bot` | README:43, dnk.maude:33 | Dummy policy with no behavior |
| `N ; D` (policy sequencing) | `arg1 ; arg2` | README:44, dnk.maude:27-28 | NetKAT policy followed by DyNetKAT term |
| `x ! N` (send) | `arg1 ! arg2` | README:45, dnk.maude:9 | Send NetKAT policy through channel |
| `x ? N` (receive) | `arg1 ? arg2` | README:45, dnk.maude:9 | Receive NetKAT policy on channel |
| `D || D` (parallel) | `arg1 || arg2` | README:46, dnk.maude:29 | Parallel composition |
| `D o+ D` (choice) | `arg1 o+ arg2` | README:47, dnk.maude:26 | Nondeterministic choice |
| `rcfg(x, N)` (reconfiguration) | `rcfg(arg1, arg2)` | README:48, dnk.maude:34 | Pinpoint a communication step |
| `X` (recursive variable) | variable name | README:49, dnk.maude:37-39 | Recursive variable, defined in JSON |

**Note:** The pipe operator `a | b` (communication merge) is internal to the axiomatization
(dnk.maude:30, 67-70) and is not a user-facing construct. It is used internally by axioms A12-A15.

### 4.3 Communication term encoding (preprocessing)

**Confirmed (`preprocess.maude:49-53`):** During preprocessing, communication terms
`x ! N` and `x ? N` are tagged with `@Comm(x, N)` while NetKAT policies are tagged
with `@NetKAT(N)`. The `parseCond` predicate distinguishes NetKAT terms (strings that
parse as NetKAT) from communication/channel terms.

---

## 5. Verification Procedure

**Confirmed (from `dynetkat.py:decide` method, lines 125-154):**

### 5.1 Analysis pipeline

The `decide(data)` method implements the following pipeline:

1. **Compute encapsulation set** (`compute_encapsulation_set`, `dynetkat.py:20-27`):
   For each communication term extracted from the program, generates `delta_H` restriction set entries.

2. **For each packet + property:** Build the analysis term:
   ```
   delta{H}(pi{n}(program))
   ```
   where `H` is the set of all `x ! Z` and `x ? Z` terms (encapsulation set),
   and `n` is the user-specified maximum unfoldings. This is constructed in
   `dynetkat.py:144`.

3. **Preprocessing step** (`preprocess.py:78-129`):
   - Parses each recursive variable with Maude (`preprocess.maude`)
   - Extracts NetKAT sub-terms via `@NetKAT(...)` tags
   - Calls the NetKAT decision procedure to check if each NetKAT sub-term equals 0
   - Rewrites zero-valued terms to `zero` in recursive variable definitions
   - Generates the final Maude module using `dnk.maude`

4. **Property checking step** (`dynetkat.py:54-94`):
   - For each property, replaces `@Program` with the analysis term
   - For each property, replaces `{}` (RSet placeholder) with `, RSet:TermSet`
   - Calls Maude to evaluate the `head`/`tail` extraction (producing a NetKAT term)
   - Calls the NetKAT decision procedure to compare two NetKAT terms for equivalence
   - Classifies result as "satisfied", "violated", or "error"

### 5.2 Reachability property checking

**Confirmed (`dynetkat.py:72-77`):** For reachability (`r`):
- Constructs term: `(in_packet) . (network_policy) . (out_packet)`
- Calls NetKAT: `equiv term1 "zero"` (checks if the composed relation equals the empty relation)
- If `prop_result == "!0"`: satisfied when result is `"false"` (not equivalent to zero -> reachable)
- If `prop_result == "=0"`: satisfied when result is `"true"` (equivalent to zero -> unreachable)

### 5.3 Waypointing property checking

**Confirmed (`dynetkat.py:78-85`):** For waypointing (`w`):
- Constructs two terms:
  - `term1 = in . network . out + in . (~out . network)* . wp . (~in . network)* . out`
  - `term2 = in . (~out . network)* . wp . (~in . network)* . out`
- Calls NetKAT: `equiv term1 term2` (checks if the two relations are equivalent)
- Satisfied when result is `"true"`

### 5.4 Output classification

**Confirmed (`dynetkat.py:97-122`, `dynetkat.py:84-93`):**

- **Reachability (`r`):**
  - `satisfied`: `(v == "false" and prop_result == "!0")` or `(v == "true" and prop_result == "=0")`
  - `violated`: otherwise
- **Waypointing (`w`):**
  - `satisfied`: `v == "true"` (terms equivalent)
  - `violated`: otherwise
- **Error:** If Maude or NetKAT tool returns `None` (parse/execution failure)

### 5.5 Timing output

**Confirmed (`dnk.py:96-100`):** When `-s` flag is set, prints:
- Total time
- Preprocessing time
- Max NetKAT decision time (across all properties)

---

## 6. Dynamic-Network Analysis Capabilities

### 6.1 Restriction operator (delta)

**Confirmed (`dnk.py:144`, `dynetkat.py:20-27`, `dnk.maude:35, 72-79`):**
- Computes the set `H` of all communication actions `x ! Z` and `x ? Z` from the program
- Wraps the program as `delta_H(pi_n(program))` — restriction eliminates the communication terms (sets them to `bot`), leaving only NetKAT policies for the final decision check
- Maude equations `[D-receive]`, `[D-send]`, `[D-rcfg]`, `[D-bot-receive]`, `[D-bot-send]`, `[D-bot-rcfg]`, `[D-plus]` implement the restriction semantics

### 6.2 Projection operator (pi_n)

**Confirmed (`dnk.py:144`, `dnk.maude:36, 83-90`):**
- `pi_n(program)` unfolds recursive variables up to `n` steps
- `pi_0(P) = bot`, `pi_{n+1}(at; p) = at; pi_n(p)`
- Applied before restriction: `delta_H(pi_n(program))`
- User-specified `n` controls the bounded unfolding depth

### 6.3 head() operator — current configuration extraction

**Confirmed (`dnk.maude:130-131, 141-143`):**
```
head(bot) = zero
head(Z ; D) = Z + head(D)
head(D o+ Q) = head(D) + head(Q)
head(rcfg(X, Z) ; D) = zero
```
- `head(D)` extracts the NetKAT policy representing the **current configuration** of DyNetKAT term `D`
- It sums all leading NetKAT policies, ignoring communication steps (which produce `zero`)
- Used in reachability/waypointing property formulas as `head(@Program)`

### 6.4 tail() operator — post-synchronization policy extraction

**Confirmed (`dnk.maude:132, 145-149`):**
```
tail(bot, RS) = bot
tail(Z ; D, RS) = tail(D, RS)
tail(D o+ Q, RS) = tail(D, RS) o+ tail(Q, RS)
tail(rcfg(X, Z) ; D, RS) = D o+ tail(D, RS)  if rcfg(X, Z) in RS
tail(rcfg(X, Z) ; D, RS) = bot              if rcfg(X, Z) not in RS
```
- `tail(D, R)` extracts the DyNetKAT policy that appears **after** the synchronization events in set `R`
- If a `rcfg(X, Z)` step is in `R`, it yields the continuation `D` plus the recursive tail
- If a `rcfg(X, Z)` step is NOT in `R`, it produces `bot` (blocks that path)
- Used in properties as `tail(@Program, {rcfg(...)})` to check post-synchronization behavior

### 6.5 Property checking approach

**Confirmed from README.md:73-82 and `dynetkat.py:144`:**

The verification flow is:
1. Apply `pi_n` (projection/unfolding) with user-specified bound `n`
2. Apply `delta_H` (restriction) to eliminate communication actions
3. Use `head` to extract the current NetKAT policy
4. Use `tail` to extract post-synchronization policies
5. Compare two NetKAT terms using the external decision procedure

---

## 7. Recursion and Unfolding Behavior

### 7.1 Recursion support

**Confirmed (`dnk.maude:37-39`, `dnk.maude:96-125`, README.md:49):**
- Recursive variables `X` are user-defined in the JSON input's `recursive_variables` dict
- Each recursive variable has a unique defining equation `X = D`
- Recursion is restricted to **guarded recursion**: a policy must be applied before changing state to a new recursive definition (paper p. 253)

### 7.2 On-demand unfolding

**Confirmed (`dnk.maude:109-122` — `RECURSIVE-DNA` module):**
```
--- unfolding the recursive variables at once is very inefficient.
--- we perform the unfolding on the fly when it is necessary
--- i.e. when the index of pi operator is still a positive integer
--- and the execution cannot continue because the terms are not guarded.

ceq unfold(P || Q) = unfold(P) || Q if (P :: UnguardedTerm) .
ceq unfold(P ||< Q) = unfold(P) ||< Q if (P :: UnguardedTerm) .
ceq unfold(P | Q) = unfold(P) | Q if (P :: UnguardedTerm) .
ceq unfold(P) = getRecPol(P) if (P :: Recursive) .
```
- Unfolding is **lazy/on-the-fly**: recursive variables are only unfolded when `pi_n` still has remaining steps AND the term is not guarded
- This avoids the inefficiency of unfolding all recursive variables at once
- The `notUnfolded` predicate tracks whether a term has been unfolded

### 7.3 Zero-elimination in preprocessing

**Confirmed (`preprocess.py:108-126`):**
- During preprocessing, each NetKAT sub-term inside recursive variables is checked for equivalence to `zero` (drop)
- If `equiv(term, "zero")` returns `true`, the term is replaced with `zero` in the recursive variable definition
- This enables the axiom `zero ; P = bot` (`dnk.maude:46`) to simplify the expression

---

## 8. Output Formats and Diagnostic Information

### 8.1 Console output

**Confirmed (`dnk.py:86-100`):**
- For each (packet, property) pair, prints one line:
  - `Packet: {packet} - property: #{prop_num}: property satisfied.`
  - `Packet: {packet} - property: #{prop_num}: property violated.`
  - `Packet: {packet} - property: #{prop_num}: an error occurred while checking this property.`
- With `-s` flag, prints timing breakdown:
  - `Total time: X.XX seconds`
  - `Preprocessing time: X.XX seconds`
  - `NetKAT time: X.XX seconds`

### 8.2 Output files

**Confirmed (`dnk.py:63-67`):**
- If not preprocessed, writes `output/{module_name}_preprocessed.json` containing the preprocessed input (with `comm` set serialized as list)
- Temporary Maude output files are created and cleaned up (`output_{name}.txt` in the project root)

---

## 9. Example Networks and Test Fixtures

### 9.1 Stateful Firewall (`benchmarks/stateful_firewall.json`)

**Confirmed:** Models the firewall from Figure 3 of the paper.

- **Recursive variables:**
  - `Switch`: `(port = int) . (port <- ext) ; Switch o+ (port = ext) . zero ; SwitchPrime`
  - `SwitchPrime`: `(port = int) . (port <- ext) ; SwitchPrime o+ (port = ext) . (port <- int) ; SwitchPrime o+ (secConEnd ? "one") ; Switch`
  - `Host`: `(secConReq ! "one") ; Host o+ (secConEnd ! "one") ; Host`
- **Program:** `Init = Host || Switch` (`program: "Host || Switch"`)
- **Channels:** `["secConReq", "secConEnd"]`
- **Packets:** `int_to_ext` and `ext_to_int` ingress/egress pairs
- **Properties (2 unfoldings):**
  1. `(r, head(@Program), "!0", 2)` — reachability: can `int_to_ext` reach egress?
  2. `(r, (head(tail(@Program, {rcfg(secConReq, "one")})))", "!0", 2)` — reachability after secConReq

### 9.2 Distributed Controller

**Confirmed (`benchmarks/distributed_controller_python` + JSON files):**

Generates two variants (`./distributed_controller.py` produces both JSON files):

1. **Independent controllers** (`distributed_controller_independent.json`):
   - Program: `SDN-1 || C1 || C2`
   - 6 switches (S1-S6), 2 controllers (C1, C2)
   - Channels: `upS1` through `upS6`
   - Properties: reachability with 2 and 3 unfoldings

2. **Synchronized controllers** (`distributed_controller_synchronized.json`):
   - Same switch topology, adds `syn` channel for controller synchronization
   - Controllers send/receive synchronization signal before flow updates
   - Same property structure with 2 and 3 unfoldings

### 9.3 FatTree benchmarks (`benchmarks/fattree.py`)

**Confirmed (`fattree.py`, `run_fattree.sh`):**

- Generates FatTree topologies with `pods` in {6, 8, 10, 12, 14, 16}
- For `pods=6`: 54 hosts, 72 aggregate switches, 9 core switches (931 total switches)
- For `pods=16`: 1024 hosts, 512 aggregate switches, 256 core switches (1792 total switches)
- Topology generated via `networkx` library
- Properties:
  - Reachability-I (property `0`): non-SSH packets reach egress (unfoldings 2-5)
  - Reachability-II (property `1`): SSH packets never reach egress (unfoldings 3-5)
  - Waypointing (property `2`): firewall `Ax0` is waypoint between ToRs (5 unfoldings)

**Confirmed run script (`run_fattree.sh:1-11`):**
```bash
for pods in 6 8 10 12 14 16; do
  for prop in reachability_1 reachability_2 waypointing all_properties; do
    python3 dnk.py ./maude-3.1/maude.linux64 ./netkat/.../katbv ./benchmarks/fattree_{pods}_{prop}.json -s
  done
done
```

---

## 10. Available Verification Properties

### 10.1 Reachability

**Confirmed (from paper text p. 912-913, README.md:65-68, `dynetkat.py:72-77`):**

Reachability: an egress point `out` is reachable (or not) from an ingress point `in`:
```
in . (p . t)* . out  != 0    (reachable)
in . (p . t)* . out  == 0    (unreachable)
```

In the tool, this is checked by:
1. Extracting the current configuration via `head(D)` to get NetKAT policy `p`
2. Composing `in . p . out` as a NetKAT term
3. Checking equivalence against `zero` via the NetKAT decision procedure

### 10.2 Waypointing

**Confirmed (from paper text p. 923-926, README.md:69, `dynetkat.py:78-85`):**

Waypointing: an intermediate point `w` is a waypoint between `in` and `out` if all packets from `in` to `out` pass through `w`:
```
in . (~out . p)* . w . (~in . p)* . out  ==  in . (~out . p)* . w . (~in . p)* . out  +  in . p . out
```

In the tool, this is checked by comparing two NetKAT terms (one with and one without the direct path) for equivalence.

---

## 11. Axiomatization (from Maude `dnk.maude`)

### 11.1 NetKAT axioms (ENK)

**Confirmed (`dnk.maude:46-48`):**
- `zero ; P = bot` — zero sequential composition (drop followed by anything deadlocks)
- `(N + Z) ; R = N ; R o+ Z ; R` (A1) — distributes choice over sequencing
- `P + P = P` (A3) — idempotence
- `P + bot = P` (A4) — identity for choice

### 11.2 DyNetKAT axioms (EDNK, A0-A15 + AIP)

**Confirmed (`dnk.maude:46-90`, paper text p. 576-623):**

The axiomatization is implemented as Maude equations (`eq`/`ceq`) in `dnk.maude`:

| Axiom | Maude source | Description |
|---|---|---|
| (A0) | `dnk.maude:48` | `(N + Z) ; R = N ; R o+ Z ; R` |
| (A1) | `dnk.maude:49` (comment) | Commutativity added to `o+` |
| (A2) | `dnk.maude:50` (comment) | Associativity added to `o+` |
| (A3) | `dnk.maude:51` | `P + P = P` |
| (A4) | `dnk.maude:52` | `P + bot = P` |
| (A5) | `dnk.maude:53` (comment) | Commutativity added to `||` |
| (A6) | `dnk.maude:54` (comment) | Associativity added to `||` |
| (A7) | `dnk.maude:55` | `P || bot = P` |
| (A8) | `dnk.maude:56` | `P || Q = (P ||< Q) o+ (Q ||< P) o+ (P \| Q)` (conditional: guards) |
| (A9) | `dnk.maude:57` | `bot ||< P = bot` |
| (A10) | `dnk.maude:59-62` | Left-merge distributes over NetKAT/Comm/rcfg sequencing |
| (A11) | `dnk.maude:64` | `(P + Q) ||< R = (P ||< R) + (Q ||< R)` |
| (A12) | `dnk.maude:66` | `(X?N ; Q) \| (X!N ; R) = rcfg(X, N) ; (Q || R)` |
| (A13) | `dnk.maude:67` | `(P + Q) \| R = (P \| R) + (Q \| R)` |
| (A14) | `dnk.maude:68` (comment) | Commutativity added to `\|` |
| (A15) | `dnk.maude:69` | `P \| Q = bot` (owise, i.e. when no sync possible) |
| (AIP) | Not in Maude | Approximation Induction Principle (paper p. 613): `p = q if forall n: pi_n(p) = pi_n(q)` |

**Restriction axioms (delta):**

| Rule | Maude source | Description |
|---|---|---|
| (delta; ) | `dnk.maude:73` | `delta{H}(N ; Q) = N ; delta{H}(Q)` |
| (delta; bot) | `dnk.maude:72` | `delta{H}(bot) = bot` |
| (delta; receive) | `dnk.maude:74` | `delta{H}((X?N);Q) = (X?N);delta{H}(Q)` if not in H |
| (delta; send) | `dnk.maude:75` | `delta{H}((X!N);Q) = (X!N);delta{H}(Q)` if not in H |
| (delta; rcfg) | `dnk.maude:76` | `delta{H}((rcfg(X,N));Q) = (rcfg(X,N));delta{H}(Q)` if not in H |
| (delta; bot; receive) | `dnk.maude:77` | `delta{H}((X?N);Q) = bot` if `(X?N) in H` |
| (delta; bot; send) | `dnk.maude:78` | `delta{H}((X!N);Q) = bot` if `(X!N) in H` |
| (delta; bot; rcfg) | `dnk.maude:79` | `delta{H}((rcfg(X,N));Q) = bot` if `(rcfg(X,N)) in H` |
| (delta; plus) | `dnk.maude:80` | `delta{H}(P + Q) = delta{H}(P) + delta{H}(Q)` |

**Projection axioms (pi_n):**

| Rule | Maude source | Description |
|---|---|---|
| (Pi-0) | `dnk.maude:83` | `pi{0}(P) = bot` |
| (Pi-1) | `dnk.maude:84` | `pi{M}(bot) = bot` |
| (Pi-netkat) | `dnk.maude:85` | `pi{s(M)}(N ; Q) = N ; pi{M}(Q)` |
| (Pi-receive) | `dnk.maude:87` | `pi{s(M)}((X?N);Q) = (X?N);pi{M}(Q)` |
| (Pi-send) | `dnk.maude:88` | `pi{s(M)}((X!N);Q) = (X!N);pi{M}(Q)` |
| (Pi-rcfg) | `dnk.maude:89` | `pi{s(M)}((rcfg(X,N));Q) = (rcfg(X,N));pi{M}(Q)` |
| (Pi-plus) | `dnk.maude:90` | `pi{s(M)}(P + Q) = pi{s(M)}(P) + pi{s(M)}(Q)` |

### 11.3 head/tail operators (property extraction)

**Confirmed (`dnk.maude:130-131, 141-149`, paper p. 969-985):**

```
head(bot) = zero
head(Z ; D) = Z + head(D)          -- extract leading NetKAT policy + recurse
head(D o+ Q) = head(D) + head(Q)    -- union over choices
head(rcfg(X, Z) ; D) = zero        -- rcfg steps produce zero

tail(bot, RS) = bot
tail(Z ; D, RS) = tail(D, RS)       -- skip non-rcfg steps
tail(D o+ Q, RS) = tail(D, RS) o+ tail(Q, RS)
tail(rcfg(X, Z) ; D, RS) = D o+ tail(D, RS)  if rcfg(X, Z) in RS
tail(rcfg(X, Z) ; D, RS) = bot     if rcfg(X, Z) not in RS
```

These implement the paper's `head` and `tail` operators (Section 5, paper p. 932-936).
They assume the input DyNetKAT term is already in normal form (restriction operator
applied, no `x?Z` or `x!Z` terms remain).

---

## 12. Benchmarks and Performance Measurements

### 12.1 FatTree experiments

**Confirmed (paper text p. 1016-1028, `fattree.py`, `run_fattree.sh`):**

The tool was evaluated on FatTree topologies with pods in {6, 8, 10, 12, 14, 16}:

| Pods | Hosts | Core + Agg switches | Total switches |
|---|---|---|---|
| 6 | 54 | 81 | 931 |
| 8 | 128 | 192 | 1504 |
| 10 | 250 | 375 | 2125 |
| 12 | 432 | 648 | 2784 |
| 14 | 686 | 1029 | 3552 |
| 16 | 1024 | 1536 | 4352 |

**Scenario:** Two ToR switches `Ta`, `Tb` in different pods. Firewall initially at
aggregation switch `Ax`, then migrated to `Ax0`. Controller performs 4 updates.

**Properties checked (per paper p. 1016-1018):**
1. (i) Non-SSH packets from `Ta` always reach `Tb` during updates
2. (ii) SSH packets from `Ta` never reach `Tb` during updates
3. (iii) After all updates, `Ax0` is a waypoint between `Ta` and `Tb`

**Hardware:** Ubuntu 20.04 LTS, Intel i9-9980HK (16 cores), 64 GB RAM.

**Results (from paper Figure 8, p. 1100-1104):**
- Preprocessing is a significant fraction of total time (independent of property)
- Individual properties checkable in < 2s for networks with < 100 switches
- Up to 5 min (reachability) / 11 min (waypointing) for largest networks (1344 switches)
- ~87% of post-preprocessing time is spent in the NetKAT decision procedure
- Checking all properties in parallel adds ~24% overhead

---

## 13. Documented Limitations and Assumptions

### 13.1 External solver dependency

**Confirmed (README.md:17-19, 25, `install.sh:7-16`):**
- The tool requires Maude >= 3.0 (downloaded separately)
- The NetKAT decision procedure must be installed separately from `https://github.com/netkat-lang/netkat/`
- No bundled solvers; the tool is purely a Python orchestrator

### 13.2 Finite domains assumption

**Confirmed (paper text p. 291-296):**
> "we work with packet fields ranging over finite domains"

The tool relies on this for the finiteness of the NetKAT normal-form decomposition
(Lemma 4, paper p. 678). This is a fundamental assumption — the analysis does not
support infinite field value domains.

### 13.3 Bounded unfolding

**Confirmed (`dynetkat.py:144`, paper p. 958):**
- The projection operator `pi_n` uses a user-specified bound `n`
- The paper states: "in practice the parameter n in pi_n is a fixed value specified by the user"
- This is an over-approximation: properties verified with bound `n` may not hold for larger unfoldings
- The AIP axiom (paper p. 613) theoretically removes this limitation but is not implemented as a decision procedure

### 13.4 Known issues

**Confirmed (README.md:140-142):**
> "We observed that in certain cases the `netkat-idd` tool raises the following error:
> `(Invalid_argument "union: not right-associative!")`. You may want to use the
> `netkat-automata` tool in these cases."

- The NetKAT-idd tool has a limitation with certain expression structures
- Workaround: use `netkat-automata` backend instead

### 13.5 Per-packet consistency

**Confirmed (paper text p. 320-322):**
> "communication in DyNetKAT guarantees preservation of well-defined behaviours when
> transitioning between network configurations. This corresponds to the so-called
> per-packet consistency."

The analysis assumes each data-plane packet sees exactly one set of flow tables
throughout its flight — an assumption from [16] (Reitblatt et al.).

---

## 14. Evidence Classification

### Confirmed implemented behavior

- All functionality documented in README.md is implemented in the source code
- The analysis pipeline (preprocessing -> head/tail extraction -> NetKAT equivalence check) is verified by reading `dnk.py`, `dynetkat.py`, `preprocess.py`, `maude_parser.py`, and `netkat_parser.py`
- The Maude axioms in `dnk.maude` directly implement the paper's A0-A15 + restriction/projection axioms

### Documented claims not independently verified

- **Performance numbers** (Section 12): Taken from paper Figure 8 text; the tool was not executed during this audit
- **AIP soundness** (paper Lemma 9, p. 735): The AIP axiom is cited in the paper but is not implemented as a Maude equation — it is a meta-level reasoning principle

### Features described in the paper but not in the tool

- **Full bisimulation** (Definition 2, paper p. 471): The tool does not implement bisimulation checking directly; it reduces to NetKAT equivalence checking via the axiomatization
- **Safety analysis framework** (Section 4, paper p. 776-900): The `head`/`tail` operators implement the core extraction mechanism, but the full safety property semantics map (Definition 11, paper p. 818) and `hregexp` syntax are not implemented as user-facing constructs — they are encoded via NetKAT equivalences
- **Extended DyNetKAT syntax** (paper Eq. 2, p. 638): The `T` (left-merge) and `|` (communication-merge) operators exist in the Maude axioms but are not user-facing syntax — they are internal to the axiomatization

### Unknown or unsupported capabilities

- **Arbitrary topologies:** The tool supports FatTree via the `fattree.py` generator. Other topology generators (e.g., arbitrary networkx graphs) are not bundled
- **Incremental verification:** No support for incremental property checking as configurations evolve — each property check is independent

---

## 15. Files Referenced

| File | Role in audit |
|---|---|
| `README.md` | Primary source for encoding, usage, capabilities |
| `dnk.py` | CLI entry point, option parsing, output formatting |
| `src/python/dynetkat.py` | Core analysis logic (head/tail, reachability, waypointing) |
| `src/python/preprocess.py` | Preprocessing (NetKAT zero-elimination, Maude file generation) |
| `src/python/maude_parser.py` | Maude subprocess wrapper |
| `src/python/netkat_parser.py` | NetKAT decision procedure wrapper |
| `src/python/util.py` | File/process utilities |
| `src/maude/dnk.maude` | Main Maude module: axioms A0-A15, delta/pi/head/tail, recursion |
| `src/maude/preprocess.maude` | Preprocessing Maude module: parse condition annotations |
| `benchmarks/stateful_firewall.json` | Example 1: stateful firewall input |
| `benchmarks/distributed_controller.py` | Example 2: distributed controller generator |
| `benchmarks/distributed_controller_independent.json` | Example 2a output |
| `benchmarks/distributed_controller_synchronized.json` | Example 2b output |
| `benchmarks/fattree.py` | FatTree topology generator |
| `benchmarks/util.py` | Helper for recursive variable computation |
| `run_test.sh` | Example invocation for stateful firewall |
| `run_fattree.sh` | Example invocation for FatTree experiments |
| `install.sh` | Dependency installation script |
| `paper.pdf` | Conference-style manuscript bundled in v1.1 |


## v1.1 feature parity

This table is the current parity ledger. It uses the immutable
[University of Twente GitLab v1.1 checkout](https://gitlab.utwente.nl/fmt/dynetikat/-/tree/1c6bd422377853378c7516a7875009fcfb5ba881).
The tag and default branch resolve to `1c6bd422377853378c7516a7875009fcfb5ba881`,
with Git tree `b90170418efdee4842cd2acab6a03f68b9a82d6a`. The GitHub copy
has the same tree. The earlier audit above is historical. The actual
Python entry point, Maude modules, adapters, JSON fixtures and scripts
supply the evidence below. The bundled `paper.pdf` is a conference-style
manuscript. The [conformance inventory](PAPER_CONFORMANCE.md) uses Springer
as the published edition. [Pinned GitHub mirror](https://github.com/hcantunc/DyNetiKAT/commit/1c6bd422377853378c7516a7875009fcfb5ba881).

| Original tool capability | Original input or output behavior | Current Lean implementation | Missing work | Required correctness theorem | Regression or benchmark needed |
|---|---|---|---|---|---|
| Program text | `program` is a DyNetKAT term string. Maude `DNA` accepts `bot`, quoted NetKAT prefix with `;`, `x ! "N"`, `x ? "N"`, `\|\|`, `o+`, names and `rcfg(x,"N")`. It declares `\|\|<`, `\|`, `delta{H}(D)` and `pi{n}(D)` as well. Prefix binds tighter than parallel/merge, then choice. Quoting and associativity affect the accepted form. | Typed AST and SOS. | Parser, precedence and type diagnostics for the artifact syntax. | Parse/elaborate to the intended AST and SOS. | Parse all fixtures; ambiguous-looking terms and mixed operators. |
| Recursive declarations | `recursive_variables` maps names to body strings, generating Recursive symbols and `getRecPol(name)` equations. | `RecEnv`, `WellFormed`, graph compile with caller-supplied support. | Frontend lookup, compute support, validate duplicates, undefined names and guardedness. | D2, D6 in proof ledger. | Single declaration, self/mutual recursion, invalid references, growing parallel. |
| Channels | `channels` is a list of names declared as Maude Channel constants. | Strings and typed labels. | Parse/validate declarations and preserve label identity. | Valid declared channel names map injectively; lookup and matching preserve pairs. | Undeclared/duplicate channel, equal/unequal payloads. |
| NetKAT text | `zero`, `one`, equality, `~`, `<-`, `+`, `.`, `*`, parentheses. Program prefixes/payloads usually carry quoted strings; the backend parses and evaluates these expressions. | Fixed-domain AST, exact evaluator and zero/equivalence. | Parse the dialect over a general schema and elaborate predicates; cover fields `sw`, `pt`, `src`, `dst`, `typ` in the fixtures. | N1–N6, especially translation of negation, typing, assignment, exact star. | Precedence, multiple writes, nested star, broad domains. |
| Ingress/egress | `in_packets` and `out_packets` map the same IDs to NetKAT predicate strings. Can specify conjunctions of multiple fields. | Caller supplies two NetKAT operands to `reachabilityPolicy`. | Typed packet-predicate input and validated pair association. | Parsed predicates and pair keys preserve the intended composed relation. | Both firewall directions; FatTree source/destination/type filters. |
| Positive reachability | Type `r`, expectation `!0`. Given extracted N, requires `in · N · out` nonempty. | `checkCondition35_correct` and graph post-event nonzero. | Positive test on any supported query expression and pair. | Nonempty iff an input/output witness exists in the selected policy. | Positive/negative initial and post-event cases. |
| Non-reachability | Type `r`, expectation `=0`. Requires the same relation to be empty. | `checkCondition34_correct` and graph initial zero. | Negative test on arbitrary supported query expressions. | Empty iff no witness exists in the selected policy. | Firewall initial isolation and SSH at each FatTree update. |
| Waypointing | Type `w`, third tuple item a waypoint predicate. Compare `A + B ≡ B`, with A and B below. | Relation equivalence primitive. | Typed waypoint expression and original verdict; path semantics for stronger claims. | Equivalence iff A⊆B. Establish exact conditions for an all-path reading. | Bypass and waypoint paths with identical endpoints, no reachable endpoints, star and non-star forms. |
| Dynamic property expressions | `@Program` is replaced by the projected/restricted program. Properties include `head(@Program)`, `head(tail(@Program,R))` and nested tails with rcfg event sets. | Graph head/tail and a two-query firewall API. | Query AST, parser, nested tail process semantics, arbitrary chosen event sets and property kinds. | S5–S8, including preservation of repeated tail and original SOS at the chosen depth. | Ordered four-update FatTree selectors, matched/unmatched events and no event. |
| Projection and unfolding | Fourth tuple item is a natural transition depth. `decide` constructs `delta{H}(pi{n}(program))`; Maude unfolds on demand for positive projection where rewriting needs an active recursive body. Zero depth returns bot. | π in AST/SOS; step and trace cutoff theorems. Certificate-based normalizer for a different executable domain. | General executable finite-depth route and sound rewrite/operational bridge. | Exact π_n finite execution, termination on guarded inputs and preservation of all packet and synchronization effects. | Depth 0/1, increasing depths, mutual recursion, growing parallel, matched event at cutoff. |
| Restriction and preprocessing | `preprocess.maude` tags communication and packet prefixes in recursive bodies. Python collects channel/payload pairs, adds both !/? forms, checks tagged NetKAT prefixes for zero and replaces proven-empty prefixes with `zero`. Maude reduces `zero;P` to bot and applies δ. | AST and graph restriction, finite table renderer blocks all unilateral sends/receives, evaluator can test zero. | Collect from the complete program including direct root occurrences, handle nested δ and retain valid handshakes, checked zero elimination. | Equivalent to source restriction and exact prefix elimination; artifact set agrees with block-all where it covers every exposed label. | Direct root communication, nested restriction, zero prefix before a productive continuation. |
| Multiple properties and packet pairs | Iterates `in_packets` keys with property entries and schedules each tuple, identified by pair key and zero-based index. | Single library call with a fixed pair and two outcomes. | Batch input and general verdict list. | Each emitted result equals its independent query on the corresponding pair. | Both firewall keys, multiple queries and a missing key diagnostic. |
| JSON / preprocessed form | Keys `module_name`, `program`, `recursive_variables`, `channels`, `in_packets`, `out_packets`, `properties`; query tuples `[type, expression, expectationOrWaypoint, depth]`. Preprocessing adds `comm`, preserves the rewritten declarations and writes `output/<module>_preprocessed.json`. | No JSON loader. | Compatibility reader, validation and checked reusable input or cache. | Parser/elaborator sound and complete for valid documented files; cached output equivalent to recomputation. | Raw and preprocessed fixtures, invalid types, invalid depth and malformed terms. |
| CLI and backend | `dnk.py <maude> <netkat> <input.json>`; `-h`, `-t/--threads` (default Pool size), `-p/--preprocessed`, `-v/--netkat-version` (`netkat-idd` default or `netkat-automata`), `-s/--time-stats`. IDD uses `katbv equiv` with files; automata writes a comparison file and passes that filename to its executable. The backend response is parsed as a Boolean. | Executable prints project name. | Usable frontend with help, worker control, reusable preprocessing and timing. External binary paths and old backend switches are implementation-specific; define any compatibility mapping. | CLI options have documented, semantics-preserving effects. | Help, fixtures, invalid args and explicit preprocessing mode. |
| Parallel checking | A multiprocessing pool checks properties and is also used for independent zero checks in preprocessing. Results are collected by key after join. | No worker dispatch. | Parallel independent queries with deterministic identity and bounded worker count. | Worker scheduling and caching preserve verdicts and key association. | Serial/parallel equality, memory and overhead at multiple worker counts. |
| Output and timing | Per packet/property satisfied, violated or error. Optional total wall time, preprocessing wall time, and **maximum** per-query NetKAT duration. Intermediate Maude/input files are implementation details. | Typed library results include extraction failure; no analysis CLI output. | Human-readable verdicts, distinct errors, stable records and separate timings. | Reported verdicts reflect the checked property and failures are never reported as mathematical decisions. | Mixed batch, errors, timing accounting, deterministic output. |
| Benchmarks | `run_test.sh` invokes the firewall JSON; controller generator and two JSON fixtures; `benchmarks/fattree.py` produces six topologies and per-group/combined files; `run_fattree.sh` runs those 24 combinations with timing. | Hand-built firewall and domain regressions. | Reproduce original fixture runs, controller variants and all FatTree scales. | Generator/fixture interpretation and S9 regression obligations. | Both firewall directions, all FatTree update prefixes, final waypoint, 6–16 pods. |
| Full paper safety language | The prototype exposes reachability/waypoint expressions and the dynamic selectors. The paper also defines trace formulas with union, concatenation, negated actions, true and finite repetition. | Firewall checks on supported inputs. | Full Definitions 12–17 and a verified usable interface to them. | Desugaring, hnf, translation, trace inclusion and exact bounded verdicts. | Forbidden prefixes, partial alphabets, positive witnesses and mixed packet/rcfg words. |

### Query and artifact details

For a starred network `N=(p·t)*`, the intended waypoint comparison uses
`A = in·N·out` and
`B = in·(¬out·p·t)*·w·(¬in·p·t)*·out`. The Python function
`insert_inside_network` tests whether the printed term contains `*` and
splices the predicate just inside its first opening parenthesis. Without a
star it prepends the predicate to N. It also strips parentheses from ingress
and egress text when building these negated predicates. Those string
operations are only justified on the intended shape. Specify the typed
formula on valid inputs, test all generated expressions and report any
differences for other inputs. Endpoint relation inclusion can hold when
one bypass path and one waypoint path connect the same pair of packets.
A path-universal claim requires an additional path observation or a
hypothesis that excludes such ambiguity.

The Maude labels on the rewrite equations are implementation-local. For
example, Maude's tagged A0 distributes NetKAT choice and its zero rule is
untagged. Use Fig. 11 identifiers for mathematical claims. The prototype
rewrites strings and uses an `owise` rule for communication merge plus
sort-sensitive on-demand unfolding. These are artifact behaviors, and
general guarded projection needs the SOS proof in the
[proof ledger](PROOF_OBLIGATIONS.md#finite-depth-projection).

Source inspection also exposes edge cases for the compatibility tests.
`preprocess.py` handles a singleton recursive declaration with
`recursive_variables.keys[0]`, which is invalid for a Python dict.
`dynetkat.py` can return `None` from a failed worker while
`report_results` unpacks each result as a pair. The IDD adapter's
`max(digits)` requires at least one number in the comparison.
Zero-prefix replacement is a string substitution across a defining body.
A repeated quoted term can occur both as a packet prefix and as a
communication payload. A typed rewrite should change only the packet
prefix, preserving synchronization and the literal event identity.
Accept valid singleton specifications and constant-only policies and
report explicit errors. These findings come from source inspection.

The FatTree generator uses shortest-path forwarding, four ordered
flow-table updates and eight reachability queries (two property groups,
each checked after one through four updates), plus one final waypoint
query. Their DyNetKAT projection depths are 2, 3, 4 and 5. The 1,344 count
at 16 pods includes 1,024 ToR endpoints (named hosts in the generator),
256 aggregation nodes and 64 core nodes. Paper timings average ten runs
and distinguish preprocessing from checking. Use separate solver,
projection/extraction, total wall time and peak-memory measurements and
record whether preprocessing was reused. The checked-in scripts show how
to generate and run the baseline. A smoke test using NetworkX 3.4.2
generated the 6-pod model with 99 nodes, 17 recursive definitions and
nine queries. The 16-pod topology constructor produced 1,344 nodes.
Running the original Maude/NetKAT pipeline and collecting comparable
benchmark results remain Phase 9 work.


### Frontend semantic boundary

The Lean executable currently prints the project name. A future DyNetKAT
parser must elaborate a paper source grammar and validate unique, defined
and guarded reachable declarations before constructing `Program`. Split
frontend validation errors from unsupported analysis or missing finite
support. Parse an analysis depth as a query parameter. Auxiliary graph
nodes, certificate tables and rendered head/tail models are internal
helper syntax.
