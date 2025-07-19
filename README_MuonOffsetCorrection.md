# Muon Offset Correction

このプログラムは、ForMuon_effで求めたoffsetをlayerごとに適用して、再度fitを行い、offsetの計算を行うためのクラスです。

## ファイル構成

### ヘッダーファイル
- `MuonOffsetCorrection.h`: メインクラスの定義

### 実装ファイル
- `MuonOffsetCorrection.cxx`: メインクラスの実装
- `MuonOffsetCorrectionMain.cxx`: メイン関数
- `MuonOffsetCorrectionExtended.cxx`: 拡張機能の実装

## 主な機能

### 1. 段階的offset補正
1. 初回解析でoffsetを計算
2. 計算されたoffsetを各layerに適用
3. 再度track fittingを実行
4. 補正後の残差を計算

### 2. 結果の比較・可視化
- 補正前後の残差分布の比較
- Layer別のoffset値の表示
- 改善度の定量評価

### 3. 詳細な解析結果
- Chi2/NDF分布の改善
- 各layerでのRMS改善率
- 効率測定結果

## 使用方法

### コンパイル
```bash
# CMakeを使用する場合
mkdir build
cd build
cmake ..
make

# 手動でコンパイルする場合
g++ -o MuonOffsetCorrection src/MuonOffsetCorrectionMain.cxx src/MuonOffsetCorrection.cxx \
    -I./include -I$(ROOTSYS)/include -L$(ROOTSYS)/lib -lRoot
```

### 実行
```bash
./MuonOffsetCorrection <dat_file> <ped_file> <dac_file> <MIP_file> <output_file> <trigger_layer0> <trigger_layer1> [save_option]
```

#### 引数説明
- `dat_file`: データファイル (.root)
- `ped_file`: ペデスタルファイル (.root)
- `dac_file`: DACキャリブレーションファイル (.root)
- `MIP_file`: MIPキャリブレーションファイル (.root)
- `output_file`: 出力ファイル名（拡張子なし）
- `trigger_layer0`: トリガーレイヤー0の番号
- `trigger_layer1`: トリガーレイヤー1の番号
- `save_option`: 保存オプション（"Save", "Print", など）

#### 実行例
```bash
./MuonOffsetCorrection data.root pedestal.root dac.root MIP.root output 0 39 Save
```

## 出力ファイル

### 主要な出力ファイル
1. `<output_file>_initial.root`: 初回解析結果
2. `<output_file>_corrected.root`: offset補正後の結果
3. `offset_correction_results_offset_comparison.png`: 比較プロット
4. `offset_correction_improvement.png`: 改善度プロット

### 含まれるヒストグラム
- `h_residual_x_before_layerN`: 補正前のX残差（layer N）
- `h_residual_y_before_layerN`: 補正前のY残差（layer N）
- `h_residual_x_after_layerN`: 補正後のX残差（layer N）
- `h_residual_y_after_layerN`: 補正後のY残差（layer N）
- `h_improvement_x`: X方向の改善度
- `h_improvement_y`: Y方向の改善度

### TTree
- `offset_values`: 各layerに適用されたoffset値

## クラス設計

### MuonOffsetCorrection クラス
主要なメソッド：
- `ProcessMuonOffsetCorrection()`: メイン処理
- `ApplyOffsetAndRefit()`: offset適用とre-fitting
- `FitMuonTrack()`: 通常のtrack fitting
- `FitMuonTrackWithOffset()`: offset適用したtrack fitting
- `CalculateOffsets()`: offset計算
- `PlotResults()`: 結果のプロット

### 内部処理フロー
1. 初回解析実行
2. 残差からoffset計算
3. Offsetを適用してre-fitting
4. 結果の比較・評価
5. 改善度の計算
6. 結果の保存・可視化

## 技術的詳細

### Offset適用方法
各layerのhitに対して、以下のように座標補正を適用：
```cpp
x_corrected = x_original - x_offset[layer]
y_corrected = y_original - y_offset[layer]
```

### Track Fitting
- TGraphErrorsを使用した直線フィット
- Chi2/NDFによる品質評価
- 外れ値の除去

### 改善度評価
- RMS改善率 = (RMS_before - RMS_after) / RMS_before × 100%
- Chi2/NDF分布の比較
- 各layerでの個別評価

## 注意事項

1. **メモリ使用量**: 大量のヒストグラムを作成するため、メモリ使用量に注意
2. **処理時間**: 2回の完全解析を行うため、処理時間が長くなる可能性
3. **入力ファイル**: 適切にキャリブレーションされたファイルが必要
4. **Layer番号**: trigger_layer0, trigger_layer1は有効な範囲内で指定

## 今後の拡張予定

1. **反復改善**: 複数回のoffset適用と改善
2. **自動収束判定**: 改善度が閾値以下になったら停止
3. **異なるfitting手法**: より高度なtrack fitting
4. **効率最適化**: メモリ使用量と処理時間の最適化

## トラブルシューティング

### よくある問題
1. **ファイルが開けない**: パスと権限を確認
2. **メモリ不足**: 処理するイベント数を制限
3. **収束しない**: 初期offset値を手動で設定
4. **結果が改善しない**: 入力データの品質を確認

### デバッグ方法
1. 中間結果の確認
2. ヒストグラムの目視確認
3. offset値の妥当性チェック
4. 統計量の確認
