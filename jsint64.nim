import math
import tables
import strutils
from algorithm import reverse

type jsInt64 = object
  low: int32
  high: int32

const digits = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"

proc parseInt(b: string, radix: int = 10): int =
  var sign = 1
  var stopIdx = 0
  if b[0] in {'-', '+'}:
    stopIdx += 1
    if b[0] == '-':
      sign = -1

  var i = 1
  result = 0

  for j in countdown(len(b)-1, stopIdx):
    let idx = find(digits, b[j])
    if idx < 0 or idx > (radix - 1):
      quit("invalid number " & $b & " for radix " & $radix, 1)
    result += idx * i
    if j > stopIdx:
      i *= radix
  return result * sign

proc toString*(n: int, base: int): string =
  result = ""
  var n = n
  var b: int
  while n >= 0:
    b = n mod base
    n = n div base
    result = $digits[b] & result
    if n == 0:
      break

proc initJsInt64*(low, high: int32): jsInt64 =
  ## Constructs a 64-bit two's-complement integer, given its low and high 32-bit
  ## values as *signed* integers.  See the from* functions below for more
  ## convenient ways of constructing Longs.
  ##
  ## The internal representation of a long is the two given signed, 32-bit values.
  ## We use 32-bit pieces because these are the size of integers on which
  ## Javascript performs bit-operations.  For operations like addition and
  ## multiplication, we split each number into 16-bit pieces, which can easily be
  ## multiplied within Javascript's floating-point representation without overflow
  ## or change in sign.
  ##
  ## In the algorithms below, we frequently reduce the negative case to the
  ## positive case by negating the input(s) and then post-processing the result.
  ## Note that we must ALWAYS check specially whether those values are MIN_VALUE
  ## (-2^63) because -MIN_VALUE == MIN_VALUE (since 2^63 cannot be represented as
  ## a positive number, it overflows back into a negative).  Not handling this
  ## case would often result in infinite recursion.
  ##
  result.low = low
  result.high = high

const ZERO = jsInt64(low: 0, high: 0)
const ONE  = jsInt64(low: 1, high: 0)
const NEG_ONE = jsInt64(low: -1, high: -1)
const MAX_VALUE = jsInt64(low: 0xFFFFFFFF'i32, high: 0x7FFFFFFF'i32)
const MIN_VALUE = jsInt64(low: 0, high: 0x80000000'i32)
const TWO_PWR_24 = jsInt64(low: 1 shl 24, high: 0)

const TWO_PWR_16_DBL = float(1 shl 16)
#const TWO_PWR_24_DBL = float(1 shl 24)
const TWO_PWR_32_DBL = float(TWO_PWR_16_DBL * TWO_PWR_16_DBL)
#const TWO_PWR_31_DBL = TWO_PWR_32_DBL / 2
#const TWO_PWR_48_DBL = TWO_PWR_32_DBL * TWO_PWR_16_DBL
const TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL
const TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2

proc isNaN*(x: SomeReal): bool = classify(x) == fcNan

proc isFinite*(x: SomeReal): bool =
  case classify(x)
  of fcInf, fcNegInf, fcNan:
    return false
  else:
    return true

proc `==`*(x, y: jsInt64): bool =
  result = x.high == y.high and x.low == y.low

proc `!=`*(x, y: jsInt64): bool =
  result = x.high != y.high or x.low != y.low

proc isZero*(x: jsInt64): bool =
  result = x.high == 0 and x.low == 0

proc isNegative*(x: jsInt64): bool = x.high < 0

proc isOdd*(x: jsInt64): bool = (x.low and 1) == 1

proc `not`*(x: jsInt64): jsInt64 =
  result.low = (not x.low)
  result.high = (not x.high)

template `inv`*(x: jsInt64): jsInt64 = `not`(x)

proc `and`*(x, y: jsInt64): jsInt64 =
  result.low = x.low and y.low
  result.high = x.high and y.high

proc `or`*(x, y: jsInt64): jsInt64 =
  result.low = x.low or y.low
  result.high = x.high or y.high

proc `xor`*(x, y: jsInt64): jsInt64 =
  result.low = x.low xor y.low
  result.high = x.high xor y.high

proc `ashr`*(x: int32, y: int32): int32 =
  let size = sizeof(int32) * 8
  if (x and (1 shl (size - 1))) == 0:
    return x shr y
  else:
    return (int32(x shr y) or int32(not 1 shl (size - y - 1)))

proc fromBits*(lowbits, highbits: int32): jsInt64 =
  ## Returns a Long representing the 64-bit integer that comes by concatenating
  ## the given high and low bits.  Each is assumed to use 32 bits.
  result.low = lowbits
  result.high = highbits

proc shiftLeft*(x: jsInt64, n: int): jsInt64 =
  var n = n and 63
  if n == 0:
    return x
  else:
    let low = x.low
    if n < 32:
      let high = x.high
      return fromBits(low shl n,
                      (high shl n) or (low shr (32 - n)))
    else:
      return fromBits(0, low shl (n - 32))
template `shl`*(x: jsInt64, n: int): jsInt64 =
  shiftLeft(x, n)

proc shiftRight*(x: jsInt64, n: int): jsInt64 =
  var n = n and 63
  if n == 0:
    return x
  else:
    let high = x.high
    if n < 32:
      let low = x.low
      return fromBits((low shr n) or (high shl (32 - n)),
                      ashr(high, n.int32))
    else:
      return fromBits(ashr(high, (n - 32).int32),
                      if high >= 0: 0 else: -1)

proc shiftRightUnsigned*(x: jsInt64, n: int): jsInt64 =
  var n = n and 63
  if n == 0:
    return x
  else:
    let high = x.high
    if n < 32:
      let low = x.low
      return fromBits((low shr n) or (high shl (32  - n)),
                      high shr n)
    elif n == 32:
      return fromBits(high, 0)
    else:
      return fromBits(high shr (n - 32), 0)


proc add*(x, y: jsInt64): jsInt64 =
  # Divide each number into 4 chunks of 16 bits, and then sum the chunks.
  var a48 = x.high shr 16
  var a32 = x.high and 0xFFFF
  var a16 = (x.low shr 16)
  var a00 = (x.low and 0xFFFF)

  var b48 = y.high shr 16
  var b32 = y.high and 0xFFFF
  var b16 = y.low shr 16
  var b00 = y.low and 0xFFFF

  var
    c48 = 0'i32
    c32 = 0'i32
    c16 = 0'i32
    c00 = 0'i32

  c00 = c00 + a00 + b00
  c16 = c16 + (c00 shr 16)
  c00 = c00 and 0xFFFF
  c16 = c16 + a16 + b16
  c32 = c32 + (c16 shr 16)
  c16 = c16 and 0xFFFF
  c32 = c32 + a32 + b32
  c48 = c48 + (c32 shr 16)
  c32 = c32 and 0xFFFF
  c48 = c48 + a48 + b48
  c48 = c48 and 0xFFFF
  return fromBits(int32((c16 shl 16) or c00), int32((c48 shl 16) or c32))

template `+`*(x, y: jsInt64): jsInt64 =
  add(x, y)

proc `+`*(x: jsInt64): jsInt64 = x

proc negate*(x: jsInt64): jsInt64 =
  if x == MIN_VALUE:
    result = MIN_VALUE
  else:
    result = add(`not`(x), ONE)

template `-`*(x: jsInt64): jsInt64 =
  negate(x)

proc subtract*(x, y: jsInt64): jsInt64 = add(x, negate(y))
template `-`*(x, y: jsInt64): jsInt64 = subtract(x, y)

proc `inc`*(x: jsInt64): jsInt64 = add(x,  ONE)
proc `dec`*(x: jsInt64): jsInt64 = subtract(x, ONE)

proc `cmp`*(x, y: jsInt64): int =
  if x == y:
    return 0
  let xNeg = isNegative(x)
  let yNeg = isNegative(y)
  if xNeg and (not yNeg):
    return -1
  if (not xNeg) and yNeg:
    return 1

  # at this point the signs are the same, so subtraction will not overflow
  if subtract(x, y).isNegative():
    return -1
  else:
    return 1

proc `<`*(x, y: jsInt64): bool = `cmp`(x, y) < 0
proc `<=`*(x, y: jsInt64): bool = `cmp`(x, y) <= 0
proc `>`*(x, y: jsInt64): bool = `cmp`(x, y) > 0
proc `>=`*(x, y: jsInt64): bool = `cmp`(x, y) >= 0

proc getLowBits*(x: jsInt64): int32 = x.low

proc getLowBitsUnsigned*(x: jsInt64): uint32 =
  if x.low >= 0:
    result = uint32(x.low)
  else:
    result = uint32(TWO_PWR_32_DBL + x.low.float)

proc getNumBitsAbs*(x: jsInt64): int =
  ## Returns the number of bits needed to represent the absolute
  if x.isNegative():
    if x == MIN_VALUE:
      return 64
    else:
      return getNumBitsAbs(negate(x))
  else:
    let val = if x.high != 0: x.high else: x.low
    var bit: int
    for bit in countDown(31, 1):
      if (val and (1 shl bit)) != 0:
        break
    return if x.high != 0: bit + 33 else: bit + 1

proc toNumber*(x: jsInt64): float64 =
  ## The closest floating-point representation to this value.
  result = x.high.float * TWO_PWR_32_DBL + getLowBitsUnsigned(x).float

proc fromNumber*(x: float64): jsInt64 =
  ## Returns a `jsInt64` representing the given value,
  ## provided that it is a finite number.
  ## Otherwise, zero is returned.

  if isNan(x) or (not isFinite(x)):
    return ZERO
  elif x <= -TWO_PWR_63_DBL:
    return MIN_VALUE
  elif (x + 1) >= TWO_PWR_63_DBL:
    return MAX_VALUE
  elif x < 0:
    return negate(fromNumber(-x))
  else:
    var low: float64 = x mod TWO_PWR_32_DBL
    var low1: int32
    var high: float64 = x / TWO_PWR_32_DBL
    var high1: int32
    when defined(js):
      {.emit: "`low1` = `low` | 0".}
      {.emit: "`high1` = `high` | 0".}
    else:
      low1 = cast[int32](int64(low))
      high1 = cast[int32](int64(high))
    return initJsInt64(low1, high1)

when defined(js):
  {.push overflowChecks: off.}
proc `*`*(x, y: jsInt64): jsInt64 =
  if x.isZero():
    return ZERO
  elif y.isZero():
    return ZERO
  elif x == ONE:
    return y
  elif y == ONE:
    return x
  elif x == NEG_ONE:
    return negate(y)
  elif y == NEG_ONE:
    return negate(x)

  if x == MIN_VALUE:
    if y.isOdd():
      return MIN_VALUE
    else:
      return ZERO
  elif y == MIN_VALUE:
    if x.isOdd():
      return MIN_VALUE
    else:
      return ZERO

  if x.isNegative():
    if y.isNegative():
      return `*`(negate(x), negate(y))
    else:
      return negate(negate(x) * y)
  elif y.isNegative():
    return negate(x * negate(y))

  # if both are small, use float multiplication
  if x < TWO_PWR_24 and y < TWO_PWR_24:
    return fromNumber(x.toNumber() * y.toNumber())

  # Divide each long into 4 chunks of 16 bits, and then add up 4x4 products.
  # We can skip products that would overflow.
  var a48 = x.high shr 16
  var a32 = x.high and 0xFFFF
  var a16 = x.low shr 16
  var a00 = x.low and 0xFFFF

  var b48 = y.high shr 16
  var b32 = y.high and 0xFFFF
  var b16 = y.low shr 16
  var b00 = y.low and 0xFFFF

  var
    c48: int32 = 0
    c32: int32 = 0
    c16: int32 = 0
    c00: int64 = 0

  # echo "a00: ", a00, " b00: ", b00, " * ", a00.float64 * b00.float64
  c00 += a00.int64 * b00.int64
  c16 += int32(c00 shr 16)
  c00 = c00 and 0xFFFF
  c16 += a16 * b00
  c32 += c16 shr 16
  c16 = c16 and 0xFFFF
  c16 += a00 * b16
  c32 += c16 shr 16
  c16 = c16 and 0xFFFF
  c32 += a32 * b00
  c48 += c32 shr 16
  c32 = c32 and 0xFFFF
  c32 += a16 * b16
  c48 += c32 shr 16
  c32 = c32 and 0xFFFF
  c32 += a00 * b32
  c48 += c32 shr 16
  c32 = c32 and 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48
  c48 = c48 and 0xFFFF
  result = fromBits(int32((c16 shl 16) or c00), int32((c48 shl 16) or c32))
when defined(js):
  {.pop.}

proc `div`*(x, y: jsInt64): jsInt64 =
  if y.isZero():
    raise newException(ValueError, "divide by zero")
  elif x.isZero():
    return ZERO

  if x == MIN_VALUE:
    if y == ONE or y == NEG_ONE: # recall that -MIN_VALUE == MIN_VALUE
      return MIN_VALUE
    elif y == MIN_VALUE:
      return ONE
    else:
      # at this point, we have |y| >= 2, so |x / y| < |MIN_VALUE|
      let halfThis = x.shiftRight(1)
      let approx = shiftLeft(`div`(halfThis, y), 1)
      if approx == ZERO:
        if y.isNegative():
          return ONE
        else:
          return NEG_ONE
      else:
        let rem = x.subtract(y * approx)
        result = approx.add(rem.div(y))
        return result
  elif y == MIN_VALUE:
    return ZERO

  if x.isNegative():
    if y.isNegative():
      return `div`(negate(x), negate(y))
    else:
      return negate(`div`(negate(x), y))
  elif y.isNegative():
    return negate(`div`(x, negate(y)))

  # Repeat the following until the remainder is less than y:  find a
  # floating-point that approximates remainder / y *from below*, add this
  # into the result, and subtract it from the remainder.  It is critical that
  # the approximate value is less than or equal to the real value so that the
  # remainder never becomes negative.
  var res = ZERO
  var rem = x
  while rem >= y:
    # Approximate the result of division. This may be a little greater or
    # smaller than the actual value.
    var approx = max(1, floor(rem.toNumber() / y.toNumber()))
    # We will tweak the approximate result by changing it in the 48-th digit or
    # the smallest non-fractional digit, whichever is larger.
    let lg2 = ceil(log2(approx))
    let delta = if lg2 <= 48: 1.0 else: pow(2.0, lg2 - 48.0)

    # Decrease the approximation until it is smaller than the remainder.  Note
    # that if it is too large, the product overflows and is negative.
    var approxRes = fromNumber(approx)
    var approxRem = approxRes * y
    while approxRem.isNegative() or approxRem > rem:
      approx = approx - delta
      approxRes = fromNumber(approx)
      approxRem = approxRes * y

    # We know the answer can't be zero... and actually, zero would cause
    # infinite recursion since we would make no progress.
    if approxRes.isZero():
      approxRes = ONE

    res = res.add(approxRes)
    rem = rem.subtract(approxRem)

  return res

proc `mod`*(x, y: jsInt64): jsInt64 =
  return x.subtract(x.div(y) * y)

proc `div`*(x: jsInt64, y: SomeNumber): jsInt64 =
  result = `div`(x, fromNumber(float(y)))

proc `div`*(x: SomeNumber, y: jsInt64): jsInt64 =
  result = `div`(fromNumber(float(x)), y)

proc `*`*(x: jsInt64, y: SomeNumber): jsInt64 =
  result = `*`(x, fromNumber(float(y)))

proc `*`*(x: SomeNumber, y: jsInt64): jsInt64 =
  result = `*`(fromNumber(float(x)), y)

proc `+`*(x: jsInt64, y: SomeNumber): jsInt64 =
  result = `+`(x, fromNumber(float(y)))

proc `+`*(x: SomeNumber, y: jsInt64): jsInt64 =
  result = `+`(fromNumber(float(x)), y)

proc `-`*(x: jsInt64, y: SomeNumber): jsInt64 =
  result = `-`(x, fromNumber(float(y)))

proc `-`*(x: SomeNumber, y: jsInt64): jsInt64 =
  result = `-`(fromNumber(float(x)), y)

proc fromInt*(value: int32): jsInt64 =
  ## returns a `jsInt64` representing the given (32-bit) integer value.
  result = initJsInt64(value, if value < 0: -1 else: 0)

proc toInt*(x: jsInt64): int32 = x.low

proc fromNumber*(value: SomeReal): jsInt64 =
  ## Returns a `jsInt64` representing the given value, provided that it
  ## is a finite number.  Otherwise, zero is returned.
  if isNan(value) or (not isFinite(value)):
    return ZERO
  elif value <= -TWO_PWR_63_DBL:
    return MIN_VALUE
  elif value >= TWO_PWR_63_DBL:
    return MAX_VALUE
  elif value < 0:
    return fromNumber(-value).negate()
  else:
    result.low = int32(value mod TWO_PWR_32_DBL)
    result.high = int32(value / TWO_PWR_32_DBL)

proc fromString*(x: string, radix = 10): jsInt64 =
  ## Returns a Long representation of the given string,
  ## written using the given radix.
  if len(x) == 0:
    raise newException(ValueError, "number format error: empty string")

  if radix < 2 or radix > 36:
    raise newException(ValueError, "invalid value for radix: " & $radix)

  if x[0] == '-':
    return negate(fromString(x[1..^1], radix))
  elif '-' in x:
    raise newException(ValueError, "number format error: interior '-' " & x)

  # Do several (8) digits each time through the loop, so as to
  # minimize the calls to the very expensive emulated div.
  var radixToPower = fromNumber(pow(radix.float, 8))
  result = ZERO
  for i in countUp(0, len(x) - 1, 8):
    let size = min(8, len(x) - i)
    let value = parseInt(x[i..(i + size - 1)], radix)
    if size < 8:
      let power = fromNumber(pow(radix.float, size.float))
      result = result * power + fromNumber(value.float)
    else:
      result = result * radixToPower
      result = result.add(fromNumber(value.float))
  return result

proc `$`*(x: jsInt64, radix = 10): string =
  if radix < 2 or radix > 36:
    raise newException(ValueError, "invalid value for radix: " & $radix)
  if x.isZero():
    return "0"
  if x.isNegative():
    if x == MIN_VALUE:
      # We need to change the Long value before it can be negated, so we remove
      # the bottom-most digit in this base and then recurse to do the rest.
      let radixLong = fromNumber(radix.float)
      let divi = `div`(x, radixLong)
      let remi = subtract(divi * radixLong, x)
      return `$`(divi, radix) & toString(remi.toInt(), radix)
    else:
      return "-" & `$`(negate(x), radix)

  # Do several (6) digits each time through the loop, so as to
  # minimize the calls to the very expensive emulated div.
  var radixToPower = fromNumber(pow(radix.float, 6))
  var rem = x
  result = ""
  while true:
    var remDiv = rem.div(radixToPower)
    var intVal = (rem.subtract(remDiv * radixToPower)).toInt()
    var digits = toString(intVal, radix)

    rem = remDiv
    if rem.isZero():
      return digits & result
    else:
      while len(digits) < 6:
        digits = "0" & digits
      result = "" & digits & result

proc high*[T: jsInt64](x: typedesc[T]): T = MAX_VALUE
proc low*[T: jsInt64](x: typedesc[T]): T = MIN_VALUE

converter toInt64*(x: jsInt64): int64 =
  result = (x.high.int64 shl 32) or x.low
converter toJsInt64(x: float64): jsInt64 =
  result = fromNumber(x)
converter toJsInt64(x: int64): jsInt64 =
  result = fromNumber(float(x))

when isMainModule:
  #echo repr(not(ONE).add(ONE))
  #echo negate(ONE)
  #echo toString(10, 10)
  var x = 62.0
  var y = fromNumber(pow(-2.0,x)+1)
  when not defined(js):
    echo "not using js"
    var yn = parseInt($y, 10)
    echo yn
  else:
    echo "using js"
    echo $y
    var yn = fromString($y, 10)
    echo yn
  echo y
  #echo (pow(2.0, x)).int
  echo y div fromNumber(10)
  echo y mod fromNumber(1000000)
  echo high(jsInt64)
  echo low(jsInt64)
  echo y div 3 * 2 
  echo jsInt64(float(high(int64)))
  echo jsInt64(high(int64))
  echo fromString($(high(int64)))
