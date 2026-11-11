To port Hypothesis's Conjecture engine to Mojo, we need to treat data generation as a deterministic parsing operation.
A strategy doesn't generate random data directly. Instead, it consumes raw choices from an underlying buffer. When the test fails, the engine manipulates this underlying buffer (shrinking it) and replays the strategy to find the minimal failing example.
Here is a structural sketch of how to implement the core ChoiceBuffer and a parameterized Strategy trait in Mojo, optimized for its compile-time lifecycle and memory model.

1. The Core Byte Provider (ChoiceBuffer)

This struct manages the raw sequence of bytes. It handles drawing data, keeping track of bounds, and reporting if a strategy asks for more data than is available (which signals the engine to treat it as a exhausted/discarded choice trail).
mojo
from memory import Span

struct ChoiceBuffer:
    var bytes: List[UInt8]
    var cursor: Int

    fn __init__(inout self, bytes: List[UInt8]):
        self.bytes = bytes
        self.cursor = 0

    fn has_capacity(self, count: Int) -> Bool:
        return self.cursor + count <= len(self.bytes)

    fn draw_byte(inout self) -> UInt8:
        """Draws a single raw choice byte."""
        if not self.has_capacity(1):
            # In a full engine, this raises an error caught by the engine 
            # to signal a "ChoiceBufferExhausted" state.
            return 0
        let val = self.bytes[self.cursor]
        self.cursor += 1
        return val

    fn draw_bytes(inout self, count: Int) -> List[UInt8]:
        """Draws a specific slice of choice bytes."""
        var out = List[UInt8](capacity=count)
        if not self.has_capacity(count):
            return out
        for _ in range(count):
            out.append(self.draw_byte())
        return out
Use code with caution.

2. The Strategy[T] Trait

Mojo traits allow us to define compile-time constraints. A strategy must know how to transform a mutable ChoiceBuffer into a concrete high-level type T.
mojo
trait Strategy[T: Movable]:
    fn draw(self, inout buffer: ChoiceBuffer) -> T:
        """Consumes bytes from the choice buffer to instantiate type T."""
        ...
Use code with caution.

3. Implementing Primitive Strategies

Let's build an integer strategy that draws an 8-bit or 64-bit integer, and a boolean strategy that uses a single byte choice.
mojo
@value
struct Int8Strategy(Strategy[Int8]):
    fn draw(self, inout buffer: ChoiceBuffer) -> Int8:
        # Cast the raw scalar byte directly to an Int8
        return Int8(buffer.draw_byte())

@value
struct BoolStrategy(Strategy[Bool]):
    fn draw(self, inout buffer: ChoiceBuffer) -> Bool:
        # Even a boolean uses a byte choice to keep byte-aligned shrinking simple
        return (buffer.draw_byte() % 2) == 1
Use code with caution.

4. Combinator Strategy: Testing Numerical Arrays / Tensors

Since you want to test numerical and tensor routines (like NuMojo arrays), you need structural strategies that first draw a structural property (like length, dimensions, or shapes) and then iteratively map primitive strategies into a collection.
Here is how a generic VectorStrategy maps a sizing bound and a primitive strategy into a sequential memory layout:
mojo
struct VectorStrategy[T: Movable, S: Strategy[T]](Strategy[List[T]]):
    var element_strategy: S
    var min_size: Int
    var max_size: Int

    fn __init__(inout self, element_strategy: S, min_size: Int, max_size: Int):
        self.element_strategy = element_strategy
        self.min_size = min_size
        self.max_size = max_size

    fn draw(self, inout buffer: ChoiceBuffer) -> List[T]:
        # 1. Determine size based on the next choice byte
        let range_width = self.max_size - self.min_size
        var size = self.min_size
        if range_width > 0:
            size += Int(buffer.draw_byte()) % (range_width + 1)
        
        # 2. Populate the structural list by pulling iteratively from the underlying buffer
        var result = List[T](capacity=size)
        for _ in range(size):
            result.append(self.element_strategy.draw(buffer))
            
        return result
Use code with caution.

How the Engine Executes this Layout

When running a property test with this design, your test framework handles execution like this:
mojo
fn test_tensor_invariant():
    # 1. The Engine generates a pseudo-random buffer of bytes
    var sample_bytes = List[UInt8](1, 5, 42, 99, 204) 
    var buffer = ChoiceBuffer(sample_bytes)
    
    # 2. Construct the high level strategy for a Vector of Int8s (length 0 to 4)
    let vec_strat = VectorStrategy[Int8, Int8Strategy](Int8Strategy(), 0, 4)
    
    # 3. Draw the structural object completely deterministically
    let my_vector = vec_strat.draw(buffer)
    
    # 4. Assert your invariant
    # if my_vector fails your validation routine, the engine takes `sample_bytes`,
    # mutates them (e.g. zeros out a byte, chops trailing bytes), and retries 
    # `vec_strat.draw(buffer)` to shrink the failure down.
Use code with caution.
Would you like to explore how to extend this pattern to support multidimensional tensor shapes (drawing dynamic Tuple or NDArray sizes), or should we look at how the engine can structure a minimal Byte-Shrinking Loop over this buffer?
