# ForMuon_eff_residual修正とMuonOffsetCorrection実装の概要

## 修正内容

### 1. ForMuon_eff_residual.cxxの修正

#### 修正点
- **offsetの保存機能を追加**
  - 計算されたoffset値をTTreeとして保存
  - `offset_values` TTreeにlayer, x_offset, y_offsetを格納
  - ヒストグラムとしても保存（h_x_offset, h_y_offset）

#### 修正箇所
```cpp
// 追加されたコード（1230行目付近）
TTree* offset_tree = new TTree("offset_values", "Calculated Offset Values");
int layer_id;
double x_offset_val, y_offset_val;

offset_tree->Branch("layer", &layer_id, "layer/I");
offset_tree->Branch("x_offset", &x_offset_val, "x_offset/D");
offset_tree->Branch("y_offset", &y_offset_val, "y_offset/D");

for (int i = 0; i < 40; ++i) {
    layer_id = i;
    x_offset_val = x_offset[i];
    y_offset_val = y_offset[i];
    offset_tree->Fill();
}

offset_tree->Write();
```

### 2. MuonOffsetCorrection.cxxの修正

#### 新機能の追加
- **LoadOffsetsFromFile関数**: 初回解析結果からoffsetを読み込む
- **ExecuteAnalysisWithOffset関数**: offsetを適用した解析を実行
- **ProcessMuonOffsetCorrection関数**: 段階的なoffset補正プロセス

#### 主要な修正点

##### LoadOffsetsFromFile関数
```cpp
int MuonOffsetCorrection::LoadOffsetsFromFile(const char* filename, double* x_offset, double* y_offset) {
    // TTreeまたはヒストグラムからoffsetを読み込み
    // エラーハンドリングを含む
}
```

##### ProcessMuonOffsetCorrection関数のStep2修正
```cpp
// 初回の結果ファイルからoffsetを読み込む
string initial_result_file = output_file + "_initial.root";
int load_result = LoadOffsetsFromFile(initial_result_file.c_str(), x_offset, y_offset);
```

### 3. RawtoRoot.hの修正

#### 新メソッドの追加
```cpp
int forMuon_eff_residual(string str_dat, string str_ped, string str_dac, string str_MIP, string output_file,int trigger_layer0, int trigger_layer1);
```

### 4. 新規作成ファイル

#### RawtoRoot_additional_methods.cxx
- 新しいメソッドの実装テンプレート

#### MuonOffsetCorrectionExample.cxx
- 使用例のサンプルコード

## 実装された機能

### 1. 段階的Offset補正プロセス
1. **Step 1**: 初回解析でoffsetを計算・保存
2. **Step 2**: 保存されたoffsetを読み込み
3. **Step 3**: offsetを適用して再解析

### 2. データの保存・読み込み
- **保存**: TTreeとヒストグラムの両方でoffsetを保存
- **読み込み**: 両方のフォーマットに対応した読み込み機能

### 3. エラーハンドリング
- ファイルの存在確認
- データの妥当性チェック
- フォールバック機能

## 使用方法

### 基本的な使用法
```cpp
MuonOffsetCorrection* corrector = new MuonOffsetCorrection();
int result = corrector->ProcessMuonOffsetCorrection(
    str_dat, str_ped, str_dac, str_MIP, 
    output_file, trigger_layer0, trigger_layer1, 
    saveornot
);
```

### 出力ファイル
- `output_initial.root`: 初回解析結果（offsetを含む）
- `output_corrected.root`: offset補正後の解析結果
- `offset_correction_results_offset_comparison.png`: 比較プロット

## 今後の拡張予定

### 1. 完全なoffset適用解析
- 現在は暫定的な実装
- 実際のtrack fittingでoffsetを適用する完全版の実装

### 2. 反復改善
- 複数回のoffset適用による精度向上
- 収束判定機能

### 3. 詳細な比較・評価
- 補正前後の詳細な比較
- 定量的な改善度評価

## 注意事項

1. **実装状況**: 現在は基本的な枠組みが完成
2. **完全性**: offset適用の詳細な実装は今後の課題
3. **テスト**: 実際のデータでのテストが必要
4. **パフォーマンス**: 大量データでの処理速度の最適化が必要

## デバッグ・トラブルシューティング

### よくある問題
1. **offset読み込み失敗**: 初回解析結果の確認
2. **ファイル権限**: 読み書き権限の確認
3. **メモリ不足**: 大量データ処理時の注意

### 確認方法
```cpp
// offset値の確認
for (int i = 0; i < Layer_No; ++i) {
    if (x_offset[i] != 0.0 || y_offset[i] != 0.0) {
        cout << "Layer " << i << ": X=" << x_offset[i] << ", Y=" << y_offset[i] << endl;
    }
}
```
