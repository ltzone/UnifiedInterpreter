module {
 func.func @live(%out: memref<2xf32>) {
  %zero = arith.constant 0.0 : f32
  %seven = arith.constant 7.0 : f32
  %buf = memref.alloc() : memref<2xf32>
  linalg.fill ins(%zero : f32) outs(%buf : memref<2xf32>)
  %view = bufferization.to_tensor %buf writable : memref<2xf32>
  linalg.fill ins(%seven : f32) outs(%buf : memref<2xf32>)
  bufferization.materialize_in_destination %view in writable %out : (tensor<2xf32>, memref<2xf32>) -> ()
  return
 }
}
