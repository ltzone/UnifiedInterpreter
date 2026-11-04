module {
 func.func @loop(%out: memref<4xf32>) {
  %lo = arith.constant 0 : i32
  %hi = arith.constant 4 : i32
  %step = arith.constant 1 : i32
  %zero = arith.constant 0.0 : f32
  %seven = arith.constant 7.0 : f32
  linalg.fill ins(%zero : f32) outs(%out : memref<4xf32>)
  scf.for %iv = %lo to %hi step %step : i32 {
   %idx = arith.index_cast %iv : i32 to index
   %slice = memref.subview %out[%idx] [1] [1] : memref<4xf32> to memref<1xf32, strided<[1], offset: ?>>
   linalg.fill ins(%seven : f32) outs(%slice : memref<1xf32, strided<[1], offset: ?>>)
  }
  return
 }
}
