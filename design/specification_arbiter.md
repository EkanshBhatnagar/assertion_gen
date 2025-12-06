# Round-Robin Arbiter Specification

## 1. Overview
The `rr_arbiter` is a parameterized hardware module designed to arbitrate access to a shared resource among multiple clients. It employs a round-robin scheduling algorithm to ensure fairness and prevent starvation.

## 2. Parameters
| Parameter | Type | Default | Description |
| :--- | :--- | :--- | :--- |
| `CLIENTS` | `int` | `4` | The number of agents (clients) requesting access. |

## 3. Interface Signals
| Signal | Direction | Width | Description |
| :--- | :--- | :--- | :--- |
| `clk` | Input | 1 | System clock (positive edge triggered). |
| `rst_n` | Input | 1 | Asynchronous active-low reset. |
| `req` | Input | `[CLIENTS-1:0]` | Request vector. Bit `i` is high if client `i` requests access. |
| `gnt` | Output | `[CLIENTS-1:0]` | Grant vector. Bit `i` is high if client `i` is granted access. |

## 4. Functional Requirements

### 4.1. Mutual Exclusion (Mutex)
* **Requirement:** At any given clock cycle, **at most one** bit in the `gnt` output vector may be asserted (Logic High).
* **Formal Property:** `$onehot0(gnt)` must always be true.

### 4.2. Validity
* **Requirement:** A grant can only be issued to a client that is currently asserting a request.
* **Formal Property:** `(gnt[i] == 1) implies (req[i] == 1)`.

### 4.3. Work Conservation
* **Requirement:** If one or more input requests (`req`) are active, the arbiter must assert a grant (`gnt`) in the same cycle. The arbiter must not remain idle if there is pending work.
* **Formal Property:** `(|req) |-> (|gnt)`.

### 4.4. Fairness (Round-Robin Policy)
* **Requirement:** The arbiter must rotate priority to ensure no client is starved.
* **Mechanism:**
    * After Client `i` is serviced (granted), the priority pointer moves to Client `i+1` (wrapping to 0 after `CLIENTS-1`).
    * If Client `i` keeps `req` high after being granted, it must lose priority to other waiting clients and wait for the priority token to return.

## 5. Timing & Reset
* **Reset Behavior:** Upon assertion of `rst_n` (low), all internal state (mask/pointer) resets. The default priority usually favors Client 0 or resets the mask to all 1s.
* **Latency:** The arbitration logic is combinational. The `gnt` output is valid in the same clock cycle as the `req` input (0-cycle latency).