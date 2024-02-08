module Utils {

// Our modules
private use CommonParameters;
private use FFI;

// System modules
private import OS.POSIX;
private use BlockDist;
private use CTypes;

proc initRuntime() {
  coforall loc in Locales do on loc {
    ls_hs_init();
  }
}

proc deinitRuntime() {
  coforall loc in Locales do on loc {
    ls_hs_exit();
  }
}

/*
record Ref {
  type eltType;
  var ptr: c_ptr(void);
  var loc: chpl_localeID_t;

  proc init(ref x : ?t) {
    this.eltType = t;
    this.ptr = __primitive("_wide_get_addr", x);
    this.loc = __primitive("_wide_get_locale", x);
  }

  proc _getReference() ref {
    assert(ptr != nil, "ptr is nil");
    // TODO: I really want to do this instead:
    // __primitive("_wide_make", eltType, ptr, loc);
    // but it doesn't seem to work :(
    return (ptr:c_ptr(eltType)).deref();
  }

  forwarding _getReference();
}
*/

inline proc sizeToDomain(dim0) { return {0 ..# dim0}; }
inline proc sizeToDomain(dim0, dim1) { return {0 ..# dim0, 0 ..# dim1}; }
inline proc sizeToDomain(dim0, dim1, dim2) { return {0 ..# dim0, 0 ..# dim1, 0 ..# dim2}; }
inline proc sizeToDomain(dim0, dim1, dim2, dim3) { return {0 ..# dim0, 0 ..# dim1, 0 ..# dim2, 0 ..# dim3}; }

proc prefixSum(count : int, arr : c_ptrConst(?eltType), sums : c_ptr(eltType),
               param inclusive : bool = false) {
  var total : eltType = 0;
  for i in 0 ..# count {
    sums[i] = total;
    total += arr[i];
  }
  if inclusive then
    sums[count] = total;
}
proc prefixSum(arr : [] ?eltType, param inclusive : bool = false) where arr.domain.rank == 1 {
  var sums : [0 ..# (if inclusive then arr.size + 1 else arr.size)] eltType;
  if arr.size == 0 then return sums;
  prefixSum(arr.size, c_ptrToConst(arr), c_ptrTo(sums), inclusive);
  return sums;
}
proc prefixSum(arr : [] ?eltType, param dim : int, param inclusive : bool = false)
    where arr.domain.rank == 2 && 0 <= dim && dim < 2 {
  const dim0 = arr.dim(0).size;
  const dim1 = arr.dim(1).size;
  select dim {
    when 0 {
      // Vertically
      var sums : [0 ..# (if inclusive then dim0 + 1 else dim0), 0 ..# dim1] eltType;
      var total : [0 ..# dim1] eltType = 0;
      for i in 0 ..# dim0 {
        POSIX.memcpy(c_ptrTo(sums[i, 0]), c_ptrToConst(total[0]),
                    dim1:c_size_t * c_sizeof(eltType));
        foreach j in 0 ..# dim1 do
          total[j] += arr[i, j];
      }
      if inclusive then
        POSIX.memcpy(c_ptrTo(sums[dim0, 0]), c_ptrToConst(total[0]),
                    dim1:c_size_t * c_sizeof(eltType));
      return sums;
    }
    when 1 {
      // Horizontally
      var sums : [0 ..# dim0, 0 ..# (if inclusive then dim1 + 1 else dim1)] eltType;
      foreach i in 0 ..# dim0 do
        prefixSum(dim1, c_ptrToConst(arr[i, 0]), c_ptrTo(sums[i, 0]), inclusive);
      return sums;
    }
    otherwise do halt("should never happen: dim=" + dim:string);
  }
}

proc sum(count : int, arr : c_ptrConst(?eltType)) {
  var total : eltType = 0;
  foreach i in 0 ..# count do
    total += arr[i];
  return total;
}
proc sum(arr : [] ?eltType)
    // ensure that arr is local
    where domainDistIsLayout(arr.domain) {
  var total : eltType = 0;
  foreach x in arr do
    total += x;
  return total;
}
proc sum(arr : [] ?eltType, param dim : int)
    where domainDistIsLayout(arr.domain) &&
          arr.domain.rank == 2 &&
          0 <= dim && dim < 2 {
  const dim0 = arr.dim(0).size;
  const dim1 = arr.dim(1).size;
  select dim {
    when 0 {
      var total : [0 ..# dim1] eltType = 0;
      for i in 0 ..# dim0 do
        foreach j in 0 ..# dim1 do
          total[j] += arr[i, j];
      return total;
    }
    when 1 {
      var total : [0 ..# dim0] eltType = 0;
      foreach i in 0 ..# dim0 do
        total[i] = sum(dim1, c_ptrToConst(arr[i, 0]));
      return total;
    }
    otherwise do halt("should never happen: dim=" + dim:string);
  }
}

record PartitionInfo {
    var _countOrOffset : int;
    var nextOffset : int;

    inline proc ref count ref { return _countOrOffset; }
    inline proc ref offset ref { return _countOrOffset; }
};

private inline proc partitionBy(in first : c_ptr(?eltType), last : c_ptr(eltType), predicate) {
    while true {
      if first == last then return last;
      if !predicate(first.deref()) then break;
      first += 1;
    }

    var it = first + 1;
    while it != last {
      if predicate(it.deref()) {
        first.deref() <=> it.deref();
        first += 1;
      }
      it += 1;
    }
    return first;
}

private inline proc swapElements(a : int, b : int, arr : c_ptr(?t1)) {
  arr[a] <=> arr[b];
}
private inline proc swapElements(a : int, b : int, arr1 : c_ptr(?t1), arr2 : c_ptr(?t2)) {
  swapElements(a, b, arr1);
  swapElements(a, b, arr2);
}

proc unstableRadixOneStep(numKeys : int, keys : c_ptr(uint(8)),
                          ref offsets : c_array(int, 257),
                          arrs...?numArrs) {
  var partitions : c_array(PartitionInfo, 256);
  foreach i in 0 ..# numKeys {
    partitions[keys[i]:int].count += 1;
  }

  var remainingPartitions : c_array(uint(8), 256);
  var numPartitions : int;
  var total : int;
  for i in 0 ..# 256 {
    const count = partitions[i].count;
    if count > 0 {
      partitions[i].offset = total;
      total += count;
      remainingPartitions[numPartitions] = i:uint(8);
      numPartitions += 1;
    }
    partitions[i].nextOffset = total;
  }

  var lastRemaining = remainingPartitions:c_ptr(uint(8)) + numPartitions;
  var endPartition = remainingPartitions:c_ptr(uint(8)) + 1;
  while lastRemaining - endPartition > 0 {
    record Func {
      inline proc this(partitionIdx : uint(8)) {
        ref beginOffset = partitions[partitionIdx:int].offset;
        ref endOffset = partitions[partitionIdx:int].nextOffset;
        if beginOffset == endOffset then return false;

        for i in beginOffset .. endOffset - 1 {
          ref offset = partitions[keys[i]:int].offset;
          keys[i] <=> keys[offset];
          swapElements(i, offset, (...arrs));
          offset += 1;
        }
        return beginOffset != endOffset;
      }
    }
    lastRemaining = partitionBy(remainingPartitions:c_ptr(uint(8)), lastRemaining, new Func());
  }

  offsets[0] = 0;
  foreach i in 1 ..# 256 {
    offsets[i] = partitions[i - 1].nextOffset;
  }
}


private proc shuffleBasedOnKeys(count : int,
                                keys : c_ptrConst(uint(8)),
                                offsets : c_ptrConst(int),
                                arr : c_ptr(?eltType)) {
  var buffer = allocate(eltType, count);
  defer deallocate(buffer);

  var current : c_array(int, 256);
  POSIX.memcpy(current, offsets, 256:c_size_t * c_sizeof(int));

  for i in 0 ..# count {
    ref offset = current[keys[i]:int];
    buffer[offset] = arr[i];
    offset += 1;
  }
  POSIX.memcpy(arr, buffer, count:c_size_t * c_sizeof(eltType));
}
private proc shuffleBasedOnKeys(count : int,
                                keys : c_ptrConst(uint(8)),
                                offsets : c_ptrConst(int),
                                arr1 : c_ptr(?),
                                arr2 : c_ptr(?)) {
  shuffleBasedOnKeys(count, keys, offsets, arr1);
  shuffleBasedOnKeys(count, keys, offsets, arr2);
}

proc stableRadixOneStep(numKeys : int, keys : c_ptrConst(uint(8)),
                        offsets : c_ptr(int), arrs...?numArrs) {
  var counts : c_array(int, 256);
  foreach i in 0 ..# numKeys do
    counts[keys[i]:int] += 1;
  // writeln(counts);
  prefixSum(256, counts:c_ptrConst(int), offsets, inclusive=true);
  shuffleBasedOnKeys(numKeys, keys, offsets, (...arrs));
  // for i in 0 ..# 10 do
  //   write(offsets[i], ", ");
  // writeln();
}

proc isBlockDist(x: blockDist(?)) param {
  return true;
}

proc isBlockDist(x) param {
  return false;
}

proc blockArrGetBlocks(ref arr : [?dom] ?eltType) where isBlockDist(arr.domain.distribution) {
  const ref targetLocales = arr.targetLocales();
  var blocks : [0 ..# targetLocales.size] (c_ptr(eltType), arr.shape.type);
  const blocksPtr = c_ptrTo(blocks);
  for (loc, i) in zip(targetLocales, 0..) {
    const ref d = arr.localSubdomain(loc);
    ref x = arr[d.low];
    const xPtr = __primitive("_wide_get_addr", x):c_ptr(eltType);
    blocks[i] = (xPtr, d.shape);
  }
  return blocks;
}

proc approxEqual(a : real, b : real, atol = kAbsTol, rtol = kRelTol) {
  return abs(a - b) <= max(atol, rtol * max(abs(a), abs(b)));
}
proc approxEqual(a : complex, b : complex, atol = kAbsTol, rtol = kRelTol) {
  return approxEqual(a.re, b.re, atol, rtol) && approxEqual(a.im, b.im, atol, rtol);
}
proc approxEqual(a : [], b : [], atol = kAbsTol, rtol = kRelTol) {
  return [i in a.domain] approxEqual(a[i], b[i], atol, rtol);
}

proc checkArraysEqual(arr1 : [] ?eltType, arr2 : [] eltType) {
  if arr1.size != arr2.size {
    writeln("Failed: array sizes differ: arr1.size=", arr1.size, " arr2.size=", arr2.size);
    halt("checkArraysEqual test failed");
  }

  const condition = if isIntegral(eltType) then arr1.equals(arr2) else && reduce approxEqual(arr1, arr2);
  if !condition {
    writeln("Failed: arrays differ:");
    var count = 0;
    const maxCount = 10;
    for (i, x1, x2) in zip(arr1.domain, arr1, arr2) {
      const f = if isIntegral(eltType) then x1 != x2 else !approxEqual(x1, x2);
      if f {
        if count >= maxCount {
          writeln("...");
          break;
        }
        writeln(i, ": ", x1, " != ", x2);
        count += 1;
      }
    }
    halt("checkArraysEqual test failed");
  }
}

} // module Utils
