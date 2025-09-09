# --- START OF FILE MCDOCRcvocr_gui.py ---


#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CVOCR(Context Vision OCR)文本识别插件 - 增强稳定版 v3.0 (2025)
作者：跳舞的火公子
完全重构，支持CVOCR最新版本，大幅增强文本检测精度和识别准确度
新增智能文本检测、高级图像预处理、自适应参数优化等功能
技术架构：PP-OCRv3 + LayoutLMv2 + Tesseract + GPT-Neo + Transformer OCR
"""

import os
import sys
import cv2
import numpy as np
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
from PIL import Image, ImageTk, ImageDraw, ImageFont, ImageEnhance, ImageFilter
import threading
import json
import time
import traceback
from datetime import datetime, timedelta
from typing import List, Dict, Optional, Union, Tuple, Any, Callable
import logging
import inspect
from pathlib import Path
import queue
from enum import Enum
import math
import re
import yaml
from collections import defaultdict, deque
import asyncio 
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import tempfile
import shutil
import platform
import subprocess
import psutil 
import functools 

try:
    import requests # ### 增强功能 1: 导入requests库用于自动下载模型
except ImportError:
    requests = None


# 版本信息
__version__ = "3.0.0"
__author__ = "跳舞的火公子"
__date__ = "2025-08-23"
__description__ = "Enhanced CVOCR GUI with Multi-Model Integration"

# 从设计系统导入设计令牌和全局设计系统实例
try:
    from design_system import design
except ImportError:
    # 如果没有design_system模块，创建一个简单的替代品
    class SimpleDesign:
        @staticmethod
        def get_color(category, shade):
            colors = {
                'neutral': {
                    '0': '#ffffff', '50': '#f9fafb', '100': '#f3f4f6', 
                    '200': '#e5e7eb', '300': '#d1d5db', '400': '#9ca3af',
                    '500': '#6b7280', '600': '#4b5563', '700': '#374151', 
                    '800': '#1f2937', '900': '#111827'
                },
                'primary': {
                    '50': '#eff6ff', '100': '#dbeafe', '200': '#bfdbfe',
                    '300': '#93c5fd', '400': '#60a5fa', '500': '#3b82f6',
                    '600': '#2563eb', '700': '#1d4ed8', '800': '#1e40af',
                    '900': '#1e3a8a'
                },
                'success': {
                    '50': '#f0fdf4', '100': '#dcfce7', '500': '#22c55e',
                    '600': '#16a34a', '700': '#15803d'
                },
                'warning': {
                    '50': '#fffbeb', '100': '#fef3c7', '500': '#f59e0b',
                    '600': '#d97706', '700': '#b45309'
                },
                'error': {
                    '50': '#fef2f2', '100': '#fee2e2', '500': '#ef4444',
                    '600': '#dc2626', '700': '#b91c1c'
                }
            }
            return colors.get(category, {}).get(str(shade), '#ffffff')
        
        @staticmethod
        def get_spacing(size):
            spacing_map = {'1': 4, '2': 8, '3': 12, '4': 16, '6': 24, '8': 32, '12': 48}
            return spacing_map.get(str(size), 8)
        
        @staticmethod
        def get_font(size, family='primary'):
            fonts = {
                'xs': ('Arial', 9), 'sm': ('Arial', 10), 'base': ('Arial', 12), 
                'lg': ('Arial', 14), 'xl': ('Arial', 16), 'body': ('Arial', 11),
                'h1': ('Arial', 24, 'bold'), 'h2': ('Arial', 20, 'bold'),
                'h3': ('Arial', 16, 'bold'), 'h4': ('Arial', 14, 'bold')
            }
            return fonts.get(size, ('Arial', 12))
        
        @staticmethod
        def configure_ttk_styles(style_manager):
            style_manager.configure('Success.TLabel', foreground='#16a34a')
            style_manager.configure('Warning.TLabel', foreground='#d97706')
            style_manager.configure('Error.TLabel', foreground='#dc2626')
        
        @staticmethod
        def apply_button_style(button, style_type):
            colors = {
                'primary': {'bg': '#2563eb', 'fg': 'white', 'active_bg': '#1d4ed8'},
                'secondary': {'bg': '#6b7280', 'fg': 'white', 'active_bg': '#4b5563'},
                'success': {'bg': '#16a34a', 'fg': 'white', 'active_bg': '#15803d'},
                'warning': {'bg': '#d97706', 'fg': 'white', 'active_bg': '#b45309'},
                'error': {'bg': '#dc2626', 'fg': 'white', 'active_bg': '#b91c1c'}
            }
            color_config = colors.get(style_type, colors['secondary'])
            button.config(
                bg=color_config['bg'], 
                fg=color_config['fg'],
                activebackground=color_config['active_bg'],
                activeforeground='white',
                relief='flat',
                bd=0,
                font=('Arial', 10),
                cursor='hand2'
            )
        
        @staticmethod
        def apply_text_style(label, style_type):
            styles = {
                'h1': {'font': ('Arial', 24, 'bold')},
                'h2': {'font': ('Arial', 20, 'bold')},
                'h3': {'font': ('Arial', 16, 'bold')},
                'h4': {'font': ('Arial', 14, 'bold')},
                'body': {'font': ('Arial', 12)},
                'body_small': {'font': ('Arial', 10)},
                'caption': {'font': ('Arial', 9), 'fg': '#6b7280'}
            }
            style_config = styles.get(style_type, {})
            label.config(**style_config)
    
    design = SimpleDesign()

# 配置日志
logging.basicConfig(
    level=logging.DEBUG, # <--- 修改为 DEBUG
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('cvocr_gui.log', encoding='utf-8')
    ]
)
logger = logging.getLogger(__name__)

# 常量定义
class CVOCRConstants:
    """CVOCR常量定义"""
    VERSION = "3.0.0"
    SUPPORTED_IMAGE_FORMATS = ['.jpg', '.jpeg', '.png', '.bmp', '.tiff', '.tif', '.webp', '.gif']
    MAX_IMAGE_SIZE = 20000  # 最大图像尺寸
    MIN_IMAGE_SIZE = 32     # 最小图像尺寸
    MAX_FILE_SIZE = 500 * 1024 * 1024  # 最大文件大小 500MB
    DEFAULT_CONFIDENCE_THRESHOLD = 60
    DEFAULT_DPI = 300
    CACHE_EXPIRE_HOURS = 24




class ModelDownloader:
    """
    一个通用的模型下载和验证辅助类。
    - 自动检查文件是否存在。
    - 通过SHA256哈希值验证文件完整性。
    - 如果文件不存在或损坏，则自动下载。
    - 提供下载进度反馈。
    """
    def __init__(self, models_info: Dict, logger_func: Callable):
        """
        初始化下载器。
        Args:
            models_info (Dict): 包含模型信息的字典。
            logger_func (Callable): 用于向GUI发送日志消息的函数。
        """
        self.models = models_info
        self.log = logger_func

    def _calculate_sha256(self, filepath: str) -> str:
        """计算文件的SHA256哈希值"""
        sha256_hash = hashlib.sha256()
        try:
            with open(filepath, "rb") as f:
                # 逐块读取以处理大文件
                for byte_block in iter(lambda: f.read(4096), b""):
                    sha256_hash.update(byte_block)
            return sha256_hash.hexdigest()
        except Exception as e:
            self.log(f"❌ 计算哈希值失败: {filepath}, 错误: {e}", "ERROR")
            return ""

    def _verify_file(self, filepath: str, expected_hash: str) -> bool:
        """验证文件的SHA256哈希值是否匹配"""
        self.log(f"🔎 正在验证文件: {os.path.basename(filepath)}...", "INFO")
        actual_hash = self._calculate_sha256(filepath)
        if actual_hash.lower() == expected_hash.lower():
            self.log(f"✅ 文件 '{os.path.basename(filepath)}' 验证成功。", "SUCCESS")
            return True
        else:
            self.log(f"⚠️ 文件 '{os.path.basename(filepath)}' 验证失败！哈希值不匹配。", "WARNING")
            self.log(f"   - 期望哈希: {expected_hash.lower()}", "DEBUG")
            self.log(f"   - 实际哈希: {actual_hash.lower()}", "DEBUG")
            return False

    def _download_file(self, url: str, filepath: str) -> bool:
        """从URL下载文件并显示进度"""
        filename = os.path.basename(filepath)
        self.log(f"🌐 开始下载: {filename}...", "INFO")
        try:
            with requests.get(url, stream=True, timeout=300) as r:
                r.raise_for_status()
                total_size = int(r.headers.get('content-length', 0))
                bytes_downloaded = 0
                last_logged_percent = -1
                
                with open(filepath, 'wb') as f:
                    for chunk in r.iter_content(chunk_size=8192):
                        f.write(chunk)
                        bytes_downloaded += len(chunk)
                        if total_size > 0:
                            percent = int((bytes_downloaded / total_size) * 100)
                            if percent > last_logged_percent and percent % 10 == 0:
                                self.log(f"   下载进度: {filename} - {percent}%", "INFO")
                                last_logged_percent = percent
            
            self.log(f"✅ {filename} 下载完成。", "SUCCESS")
            return True
        except requests.exceptions.RequestException as e:
            self.log(f"❌ 下载失败: {filename}, 错误: {e}", "ERROR")
            if os.path.exists(filepath):
                os.remove(filepath) # 删除不完整的文件
            return False
        except Exception as e:
            self.log(f"❌ 保存文件时出错: {filename}, 错误: {e}", "ERROR")
            return False

    def check_and_download_all(self) -> bool:
        """检查所有模型，如果需要则下载并验证。"""
        for model_name, info in self.models.items():
            filepath = info['filename']
            
            if os.path.exists(filepath):
                if self._verify_file(filepath, info['sha256_hash']):
                    continue  # 文件存在且完好，跳到下一个
                else:
                    self.log(f"检测到损坏文件 '{filepath}'。将删除并重新下载。", "WARNING")
                    os.remove(filepath)
            
            # 如果文件不存在或已损坏被删除，则下载
            if not self._download_file(info['url'], filepath):
                messagebox.showerror("模型下载失败", 
                                     f"无法下载关键模型文件 '{filepath}'。\n\n"
                                     "图形和表格检测功能将不可用。\n"
                                     "请检查您的网络连接和日志获取详细信息。")
                return False  # 一旦有文件下载失败，则终止
            
            # 下载后再次验证
            if not self._verify_file(filepath, info['sha256_hash']):
                messagebox.showerror("模型验证失败", 
                                     f"下载的模型文件 '{filepath}' 已损坏。\n\n"
                                     "图形和表格检测功能将不可用。\n"
                                     "请尝试重启程序或手动下载。")
                return False # 验证失败，终止

        self.log("✅ 所有YOLO模型文件均已准备就绪。", "SUCCESS")
        return True

class AdvancedTextSegmentator:
    """高级文本分割器 - 实现精确的文本行检测、字符分割和区域优化"""
    
    def __init__(self):
        self.config = {
            # 文本行检测参数
            'min_text_size': 6,
            'max_text_size': 300,
            'text_threshold': 0.6,
            'link_threshold': 0.3,
            'low_text': 0.3,
            'mag_ratio': 1.8,
            'slope_ths': 0.05,
            'ycenter_ths': 0.8,
            'height_ths': 0.8,
            'width_ths': 0.8,
            'add_margin': 0.15,
            
            # 字符分割参数
            'char_min_width': 4,
            'char_max_width': 100,
            'char_min_height': 8,
            'char_max_height': 150,
            'char_aspect_ratio_min': 0.1,
            'char_aspect_ratio_max': 5.0,
            
            # 分割质量参数
            'min_fill_ratio': 0.1,
            'max_overlap_ratio': 0.3,
            'merge_threshold': 0.5,
            'split_threshold': 0.7,
            
            # 高级分割参数
            'multi_scale_levels': 3,
            'adaptive_threshold_sizes': [7, 11, 15, 21],
            'morphology_iterations': 2,
            'connected_component_min_area': 25,
            
            # 文本方向检测
            'angle_detection_precision': 0.1,
            'text_line_merge_distance': 5,
            'text_line_height_variance': 0.3,
        }
        
        # 分割算法缓存
        self._segmentation_cache = {}
        self._cache_max_size = 15
        
        logger.info("高级文本分割器已初始化")
class EnhancedTextDetector(AdvancedTextSegmentator):
    """
    增强版文本检测器 (V4.2 - 策略组合版)
    - 允许用户通过算法列表动态组合检测策略。
    - 废除固定的精度等级，改为灵活的方法调度。
    """
    def _is_likely_punctuation(self, region_info: Dict, reference_height: float) -> bool:
        """
        通过几何特征启发式地判断一个区域是否可能是标点符号。
        Args:
            region_info (Dict): 包含区域 'rect' 信息的字典。
            reference_height (float): 用于比较的参考高度（通常是相邻文本块的高度）。
        Returns:
            bool: 如果区域可能是标点符号，则为 True。
        """
        if not region_info or reference_height <= 0:
            return False
        
        try:
            _, (w, h), _ = region_info['rect']
            # 标准化宽高
            if w < h: w, h = h, w

            # 标点符号的特征：
            # 1. 高度明显小于正常字符。
            # 2. 宽高比在一定范围内（覆盖了方形的点、逗号，以及扁平的破折号）。
            is_small_enough = h < reference_height * 0.6
            aspect_ratio = w / (h + 1e-6)
            is_aspect_ratio_ok = 0.2 < aspect_ratio < 2.5
            
            return is_small_enough and is_aspect_ratio_ok
        except Exception:
            return False


    def _aggregate_line_fragments(self, regions: List[np.ndarray]) -> List[np.ndarray]:
        """
        (V5核心) 使用凸包聚合策略，将一行内的所有碎片强制合并成一个单一的、完整的区域。
        这是一个整体性、非贪婪的合并方法。
        
        Args:
            regions (List[np.ndarray]): 已被聚类到同一行的所有文本区域碎片。

        Returns:
            List[np.ndarray]: 一个只包含单个、已合并的文本行区域的列表。
        """
        if not regions:
            return []
        
        # 如果一行只有一个碎片，直接返回，无需处理
        if len(regions) == 1:
            return regions
            
        try:
            # 将该行所有碎片的所有顶点坐标收集到一个大的列表中
            all_points = np.vstack(regions)
            
            # 计算能包围所有这些点的最小面积的旋转矩形
            merged_rect = cv2.minAreaRect(all_points)
            
            # 获取这个最终矩形的四个角点
            merged_box = cv2.boxPoints(merged_rect)
            
            # 返回只包含这一个完整行框的列表
            return [merged_box.astype(np.float32)]

        except Exception as e:
            logger.error(f"行碎片聚合失败: {e}", exc_info=True)
            # 发生错误时，安全地返回原始未合并的碎片
            return regions       
    def _merge_text_regions_in_line(self, regions: List[np.ndarray]) -> List[np.ndarray]:
        """
        智能合并在同一行内的文本区域 (V3 - 几何优化最终版)
        此版本专注于通过更精确和更宽松的几何判断来提升合并效果。
        - 回归到纯几何判断，移除了可能在新工作流下失效的像素特征分析。
        - 采用更鲁棒的水平间隙计算方法，直接比较旋转矩形的边界。
        - 适度放宽了垂直对齐和水平间隙的阈值，以合并更多合理的文本块。
        """
        if len(regions) <= 1:
            return regions

        try:
            # 步骤1: 获取每个区域的详细几何信息，包括旋转矩形和其四个角点
            regions_info = []
            for r in regions:
                # 使用 try-except 以处理无效区域，防止程序崩溃
                try:
                    rect = cv2.minAreaRect(r.astype(np.int32))
                    # cv2.boxPoints 返回旋转矩形的4个角点，这对于精确计算间隙至关重要
                    points = cv2.boxPoints(rect)
                    regions_info.append({'region': r, 'rect': rect, 'points': points})
                except cv2.error:
                    logger.warning(f"跳过无效区域，无法计算 minAreaRect。")
                    continue # 跳过这个无效区域

            # 如果没有有效的区域可供处理，直接返回
            if not regions_info:
                return regions

            # 步骤2: 按中心点的X坐标对区域进行排序，确保从左到右处理
            regions_info.sort(key=lambda item: item['rect'][0][0])

            # 步骤3: 迭代地进行分组和合并
            merged_regions = []
            if not regions_info:
                return [] # 再次检查，以防万一
            
            # 初始化第一个合并组
            current_merge_group = [regions_info[0]]

            for i in range(1, len(regions_info)):
                prev_info = current_merge_group[-1]
                current_info = regions_info[i]

                (cx_prev, cy_prev), (w_prev, h_prev), _ = prev_info['rect']
                (cx_curr, cy_curr), (w_curr, h_curr), _ = current_info['rect']
                
                # 标准化宽高，确保 h 是较短的边（近似于文本行的高度）
                if w_prev < h_prev: w_prev, h_prev = h_prev, w_prev
                if w_curr < h_curr: w_curr, h_curr = h_curr, w_curr

                # --- 步骤4: 定义并应用优化后的多维度合并条件 ---
                
                # 条件1: 垂直中心点对齐 (阈值已放宽)
                # 使用两个区域中较高者的高度作为基准
                max_height = max(h_prev, h_curr, 1) # 添加1以避免除以零
                vertical_dist = abs(cy_prev - cy_curr)
                # 只要垂直偏差小于最大高度的70%，就认为是对齐的
                is_vertically_aligned = vertical_dist < max_height * 0.7

                # 条件2: 水平间隙合理 (采用新算法，更精确，阈值已放宽)
                # 获取前一个区域的最右侧x坐标和当前区域的最左侧x坐标
                prev_max_x = np.max(prev_info['points'][:, 0])
                curr_min_x = np.min(current_info['points'][:, 0])
                # 计算它们之间的真实水平间隙
                horizontal_gap = curr_min_x - prev_max_x
                # 间隙应该为正（即不重叠），且小于一个较大的阈值（例如最大高度的3倍，允许几个字符的空格）
                is_horizontally_close = 0 <= horizontal_gap < max_height * 3.0

                # 条件3: 高度相似性 (这是一个很好的约束，保持不变)
                height_ratio = min(h_prev, h_curr) / (max_height + 1e-6) # 加epsilon防止除零
                is_height_similar = height_ratio > 0.6

                # 综合判断：三个条件必须同时满足
                if is_vertically_aligned and is_horizontally_close and is_height_similar:
                    # 如果满足，将当前区域加入正在构建的合并组
                    current_merge_group.append(current_info)
                else:
                    # 如果不满足，说明一个合并组结束了
                    # 处理上一个合并组
                    group_regions = [info['region'] for info in current_merge_group]
                    if len(group_regions) > 1:
                        # 如果组里有多个区域，将它们的所有点合并，并计算一个新的、能包围所有点的最小外接矩形
                        all_points = np.vstack(group_regions)
                        merged_rect = cv2.minAreaRect(all_points)
                        merged_box = cv2.boxPoints(merged_rect)
                        merged_regions.append(merged_box.astype(np.float32))
                    else:
                        # 如果组里只有一个区域，直接将其添加到结果中
                        merged_regions.append(group_regions[0])
                    
                    # 开启一个新的合并组，并将当前区域作为新组的第一个成员
                    current_merge_group = [current_info]

            # 步骤5: 循环结束后，不要忘记处理最后一组
            group_regions = [info['region'] for info in current_merge_group]
            if len(group_regions) > 1:
                all_points = np.vstack(group_regions)
                merged_rect = cv2.minAreaRect(all_points)
                merged_box = cv2.boxPoints(merged_rect)
                merged_regions.append(merged_box.astype(np.float32))
            else:
                merged_regions.append(group_regions[0])
                
            return merged_regions

        except Exception as e:
            # 捕获整个方法的意外错误，并记录日志
            logger.error(f"智能行合并时发生意外错误: {e}", exc_info=True)
            # 在发生错误时，安全地返回原始未合并的区域列表，避免程序崩溃
            return regions
    def detect_text_regions_advanced(self, image: np.ndarray, 
                                 enabled_algorithms: List[str]) -> Tuple[List[np.ndarray], Dict]:
        """
        高级文本区域检测 (V5 - 整体聚合版)
        - 引入两阶段“聚类-聚合”工作流。
        - 彻底放弃“成对合并”，改用基于凸包的“整体聚合”策略，从根本上解决碎片化问题。
        """
        try:
            algorithms_key = "_".join(sorted(enabled_algorithms))
            merge_status_key = f"merge_on" if self.config.get('enable_smart_line_merge', True) else "merge_off"
            cache_key = f"{hash(image.tobytes())}_{algorithms_key}_{merge_status_key}"

            if cache_key in self._segmentation_cache:
                cached_result = self._segmentation_cache[cache_key]
                logger.info("使用缓存的分割结果")
                return cached_result['regions'], cached_result['metadata']
            
            start_time = time.time()
            
            gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY) if len(image.shape) == 3 else image.copy()

            # 步骤 1: 收集所有原始、精细的候选区域
            all_raw_regions = []
            methods_used = []
            
            algorithm_map = {
                'simple_high_contrast': self._simple_high_contrast_detection,
                'improved_mser': self._improved_mser_detection,
                'multiscale_contour': self._multiscale_contour_detection,
                'gradient_based': self._gradient_based_detection,
                'multilevel_mser': lambda g: self._multilevel_mser_detection(g)[0],
                'stroke_width_transform': lambda g: self._stroke_width_transform_detection(g)[0],
                'connected_components': lambda g: self._connected_component_analysis(g)[0],
                'character_level': lambda g: self._character_level_detection(g)[0]
            }

            for algo_name in enabled_algorithms:
                if algo_name in algorithm_map:
                    try:
                        regions = algorithm_map[algo_name](gray)
                        all_raw_regions.extend(regions)
                        methods_used.append(algo_name)
                    except Exception as e:
                        logger.error(f"执行算法 '{algo_name}' 时失败: {e}")
            
            # 步骤 2: (可选) 对所有收集到的原始区域进行智能行聚合
            regions_to_optimize = []
            if self.config.get('enable_smart_line_merge', True):
                logger.info(f"收集到 {len(all_raw_regions)} 个原始区域，开始执行智能行聚合...")
                
                if not all_raw_regions:
                    regions_to_optimize = []
                else:
                    # 2a. 全局排序
                    all_raw_regions.sort(key=lambda r: (cv2.boundingRect(r.astype(np.int32))[1], 
                                                        cv2.boundingRect(r.astype(np.int32))[0]))
                    
                    # 2b. 动态行聚类
                    lines = [[all_raw_regions[0]]]
                    for i in range(1, len(all_raw_regions)):
                        current_region = all_raw_regions[i]
                        last_line = lines[-1]
                        
                        line_y_centers = [cv2.minAreaRect(r.astype(np.int32))[0][1] for r in last_line]
                        line_heights = [min(cv2.minAreaRect(r.astype(np.int32))[1]) for r in last_line]
                        
                        avg_line_y = np.mean(line_y_centers)
                        avg_line_h = np.mean(line_heights) if line_heights else 1

                        curr_cy = cv2.minAreaRect(current_region.astype(np.int32))[0][1]
                        
                        if abs(curr_cy - avg_line_y) < avg_line_h * 0.7:
                            last_line.append(current_region)
                        else:
                            lines.append([current_region])
                
                    # 2c. 【革命性改变】对每个聚类好的行，进行整体聚合
                    merged_lines = []
                    for line_regions in lines:
                        # 调用全新的、更强大的聚合函数
                        aggregated_line = self._aggregate_line_fragments(line_regions)
                        merged_lines.extend(aggregated_line)
                    
                    regions_to_optimize = merged_lines
                    logger.info(f"智能行聚合完成，区域数从 {len(all_raw_regions)} 聚合为 {len(regions_to_optimize)}。")
            else:
                logger.info("智能行聚合未启用，将直接优化原始区域。")
                regions_to_optimize = all_raw_regions

            # 步骤 3: 最终优化
            final_regions = self._optimize_text_regions(regions_to_optimize, gray.shape)
            final_regions = self._sort_regions_by_reading_order(final_regions)
            
            # 步骤 4: 整理元数据并返回
            processing_time = time.time() - start_time
            
            metadata = {
                'processing_time': processing_time,
                'detection_mode': 'custom_combination',
                'algorithms_used': methods_used,
                'total_regions': len(final_regions),
                'raw_regions_count': len(all_raw_regions),
            }
            if self.config.get('enable_smart_line_merge', True):
                metadata['merged_regions_count'] = len(regions_to_optimize)
            
            self._manage_segmentation_cache(cache_key, {'regions': final_regions, 'metadata': metadata})
            logger.info(f"高级文本检测完成: {len(final_regions)}个区域, 耗时: {processing_time:.3f}秒, 使用算法: {methods_used}")
            
            return final_regions, metadata
            
        except Exception as e:
            logger.error(f"高级文本区域检测失败: {e}", exc_info=True)
            return [], {'error': str(e)}
    def _simple_high_contrast_detection(self, gray: np.ndarray) -> List[np.ndarray]:
        """
        一个简单高效的检测方法，专门用于处理高对比度、低噪声的图像。(V2 - 增强版)
        - 增加亮度均匀化预处理，以应对轻微的光照不均。
        - 增加基于“实心度”的轮廓后过滤，以排除非文本的噪声。
        """
        try:
            regions = []
            
            # --- 新增：亮度均匀化 ---
            # 使用一个大核的模糊来估计背景光照
            blurred = cv2.GaussianBlur(gray, (55, 55), 0)
            # 从原图中除以背景，进行光照补偿
            # 添加一个小的epsilon防止除以零
            uniform_gray = (gray / (blurred + 1e-5)) * np.mean(blurred)
            uniform_gray = cv2.normalize(uniform_gray, None, 0, 255, cv2.NORM_MINMAX).astype(np.uint8)

            # 使用Otsu方法进行全局二值化
            _, binary = cv2.threshold(uniform_gray, 0, 255, cv2.THRESH_BINARY_INV + cv2.THRESH_OTSU)
            
            # 查找外部轮廓
            contours, _ = cv2.findContours(binary, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            
            img_h, img_w = gray.shape
            
            for contour in contours:
                area = cv2.contourArea(contour)
                x, y, w, h = cv2.boundingRect(contour)

                if (area > self.config['min_text_size']) and \
                   (w < img_w * 0.95 and h < img_h * 0.95):
                    
                    aspect_ratio = w / h if h > 0 else 0
                    if 0.01 < aspect_ratio < 100:
                        
                        # --- 新增：基于实心度的过滤 ---
                        hull = cv2.convexHull(contour)
                        hull_area = cv2.contourArea(hull)
                        solidity = float(area) / (hull_area + 1e-6)
                        
                        # 文本轮廓通常比较“实心”，而噪点则形状不规则
                        if solidity > 0.4:
                            rect = cv2.minAreaRect(contour)
                            box = cv2.boxPoints(rect)
                            regions.append(box.astype(np.float32))

            logger.info(f"简单高对比度检测完成，找到 {len(regions)} 个候选区域。")
            return regions
            
        except Exception as e:
            logger.error(f"简单高对比度检测失败: {e}")
            return []
    def _improved_mser_detection(self, gray: np.ndarray) -> List[np.ndarray]:
        """
        改进的MSER检测 (V3 - API兼容最终版)
        - 采用创建实例后逐一设置参数的方式，彻底解决各OpenCV版本间的关键字参数兼容性问题。
        - 保留了动态Delta、双向检测和NMS等所有增强功能。
        """
        try:
            all_regions_with_scores = []
            
            contrast_std = np.std(gray)
            delta = int(max(2, min(10, 5.0 * (contrast_std / 128.0))))
            logger.debug(f"MSER动态Delta设置为: {delta} (基于图像标准差: {contrast_std:.2f})")

            for image_pass in [gray, cv2.bitwise_not(gray)]:
                try:
                    # --- 核心修正：采用 Setter 方法配置 MSER ---
                    # 1. 创建一个默认的 MSER 对象
                    mser = cv2.MSER_create()
                    
                    # 2. 逐一调用 setter 方法来设置参数
                    mser.setDelta(delta)
                    mser.setMinArea(30)
                    mser.setMaxArea(14400)
                    mser.setMaxVariation(0.25)
                    mser.setMinDiversity(0.2)
                    # --- 修正结束 ---
                    
                    mser_regions, _ = mser.detectRegions(image_pass)
                    
                    for region in mser_regions:
                        hull = cv2.convexHull(region.reshape(-1, 1, 2))
                        rect = cv2.minAreaRect(hull)
                        box = cv2.boxPoints(rect)
                        
                        if self._validate_text_region(box, gray):
                            score = cv2.contourArea(box)
                            all_regions_with_scores.append((box, score))

                except Exception as e:
                    logger.warning(f"MSER创建或检测失败: {e}")

            if not all_regions_with_scores:
                return []

            boxes = [item[0] for item in all_regions_with_scores]
            scores = [item[1] for item in all_regions_with_scores]
            rects_for_nms = [cv2.boundingRect(box.astype(np.int32)) for box in boxes]
            
            indices = cv2.dnn.NMSBoxes(rects_for_nms, scores, score_threshold=0.1, nms_threshold=0.3)
            
            final_regions = []
            if len(indices) > 0:
                for i in indices.flatten():
                    final_regions.append(boxes[i].astype(np.float32))
            
            return final_regions
            
        except Exception as e:
            logger.error(f"改进MSER检测失败: {e}")
            return []
    
    
    def _multiscale_contour_detection(self, gray: np.ndarray) -> List[np.ndarray]:
        """
        多尺度轮廓检测 (V2 - 增强版)
        - 使用多方向形态学核（水平、垂直、方形），以适应不同方向的文本。
        - 形态学核的大小与当前处理的图像尺度动态关联。
        - 增加轮廓层级分析，以过滤掉内部孔洞等非文本轮廓。
        """
        try:
            regions = []
            scales = [0.8, 1.0, 1.2, 1.5]
            
            for scale in scales:
                if scale != 1.0:
                    h, w = gray.shape
                    new_h, new_w = int(h * scale), int(w * scale)
                    scaled_gray = cv2.resize(gray, (new_w, new_h), interpolation=cv2.INTER_LINEAR)
                else:
                    scaled_gray = gray
                
                for threshold_size in self.config['adaptive_threshold_sizes']:
                    try:
                        binary = cv2.adaptiveThreshold(
                            scaled_gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                            cv2.THRESH_BINARY_INV, threshold_size, 2
                        )
                        
                        # --- 新增：多方向和自适应大小的形态学核 ---
                        # 核的大小根据当前图像缩放比例调整
                        base_kernel_w = max(3, int(5 * scale))
                        base_kernel_h = max(3, int(5 * scale))
                        
                        kernels = [
                            cv2.getStructuringElement(cv2.MORPH_RECT, (base_kernel_w, 1)), # 水平
                            cv2.getStructuringElement(cv2.MORPH_RECT, (1, base_kernel_h)), # 垂直
                            cv2.getStructuringElement(cv2.MORPH_RECT, (3, 3))              # 方形
                        ]
                        
                        merged_morph = np.zeros_like(binary)
                        for kernel in kernels:
                            processed = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel, 
                                                       iterations=self.config['morphology_iterations'])
                            # 将不同方向处理的结果合并
                            merged_morph = cv2.bitwise_or(merged_morph, processed)

                        # --- 新增：使用轮廓层级分析 ---
                        # RETR_CCOMP 查找所有轮廓并组织成两层：外部和内部（孔洞）
                        contours, hierarchy = cv2.findContours(merged_morph, cv2.RETR_CCOMP, cv2.CHAIN_APPROX_SIMPLE)
                        
                        if hierarchy is None: continue

                        # 只处理外部轮廓 (hierarchy[0][i][3] == -1 表示没有父轮廓)
                        for i, contour in enumerate(contours):
                            if hierarchy[0][i][3] == -1:
                                area = cv2.contourArea(contour)
                                if area > self.config['connected_component_min_area']:
                                    rect = cv2.minAreaRect(contour)
                                    box = cv2.boxPoints(rect)
                                    
                                    if scale != 1.0:
                                        box = box / scale
                                    
                                    regions.append(box.astype(np.float32))
                                    
                    except Exception as e:
                        logger.warning(f"阈值{threshold_size}处理失败: {e}")
                        continue
            
            return regions
            
        except Exception as e:
            logger.error(f"多尺度轮廓检测失败: {e}")
            return []
    def _gradient_based_detection(self, gray: np.ndarray) -> List[np.ndarray]:
        """
        基于梯度的文本检测 (V2 - 增强版)
        - 使用更精确的 Scharr 算子代替 Sobel。
        - 引入梯度方向信息，过滤掉内部梯度方向混乱的非文本区域。
        """
        try:
            regions = []
            
            # --- 改进：使用 Scharr 算子 ---
            grad_x = cv2.Scharr(gray, cv2.CV_64F, 1, 0)
            grad_y = cv2.Scharr(gray, cv2.CV_64F, 0, 1)
            
            magnitude = np.sqrt(grad_x**2 + grad_y**2)
            # 梯度方向，单位为度
            angle = np.arctan2(grad_y, grad_x) * (180 / np.pi)
            
            magnitude_norm = cv2.normalize(magnitude, None, 0, 255, cv2.NORM_MINMAX).astype(np.uint8)
            
            _, binary = cv2.threshold(magnitude_norm, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            
            kernel_horizontal = cv2.getStructuringElement(cv2.MORPH_RECT, (5, 1))
            kernel_vertical = cv2.getStructuringElement(cv2.MORPH_RECT, (1, 5))
            
            horizontal = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel_horizontal)
            vertical = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel_vertical)
            
            combined = cv2.bitwise_or(horizontal, vertical)
            
            contours, _ = cv2.findContours(combined, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            
            for contour in contours:
                area = cv2.contourArea(contour)
                if area > self.config['min_text_size'] ** 2:
                    rect = cv2.minAreaRect(contour)
                    box = cv2.boxPoints(rect)
                    
                    # --- 新增：使用梯度方向进行验证 ---
                    # 文本区域内部的梯度方向应该比较集中
                    mask = np.zeros_like(gray, dtype=np.uint8)
                    cv2.fillPoly(mask, [box.astype(np.int32)], 255)
                    
                    # 提取区域内的梯度方向
                    region_angles = angle[mask > 0]
                    if len(region_angles) > 10: # 至少需要10个点才有统计意义
                        # 计算梯度方向的标准差，值越小说明方向越一致
                        angle_std = np.std(region_angles)
                        # 文本区域的梯度方向标准差通常较小
                        if angle_std < 45: # 阈值可调
                            regions.append(box.astype(np.float32))
            
            return regions
            
        except Exception as e:
            logger.error(f"梯度检测失败: {e}")
            return []
    
    def _stroke_width_transform_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """
        笔画宽度变换检测 (V2 - 增强版)
        - 实现双向追踪以获得更准确的笔画宽度。
        - 对生成的SWT图像进行中值滤波后处理。
        - 增加一个简单的字符组件合并步骤。
        """
        try:
            # 引入一个内部的 SWT 追踪函数
            def trace_stroke(x, y, grad_x, grad_y, edges, max_len=50):
                points = []
                # 沿梯度方向追踪
                for i in range(1, max_len):
                    nx = int(x + grad_x * i)
                    ny = int(y + grad_y * i)
                    if not (0 <= nx < edges.shape[1] and 0 <= ny < edges.shape[0]):
                        break
                    points.append((nx, ny))
                    if edges[ny, nx] > 0:
                        # 检查梯度是否大致相反
                        g_nx, g_ny = grad_x_norm[ny, nx], grad_y_norm[ny, nx]
                        if np.dot([grad_x, grad_y], [g_nx, g_ny]) < -0.8:
                            return points
                return None

            edges = cv2.Canny(gray, 50, 150)
            grad_x = cv2.Sobel(gray.astype(np.float32), cv2.CV_32F, 1, 0, ksize=3)
            grad_y = cv2.Sobel(gray.astype(np.float32), cv2.CV_32F, 0, 1, ksize=3)
            magnitude = np.sqrt(grad_x**2 + grad_y**2)
            grad_x_norm = grad_x / (magnitude + 1e-9)
            grad_y_norm = grad_y / (magnitude + 1e-9)

            swt = np.full(gray.shape, np.inf, dtype=np.float32)
            rays = []
            
            # 寻找边缘点并追踪
            edge_coords = np.argwhere(edges > 0)
            for y, x in edge_coords:
                gx, gy = grad_x_norm[y, x], grad_y_norm[y, x]
                ray = trace_stroke(x, y, gx, gy, edges)
                if ray:
                    stroke_width = np.linalg.norm(np.array(ray[-1]) - np.array((x,y)))
                    for p in ray:
                        swt[p[1], p[0]] = min(swt[p[1], p[0]], stroke_width)
                    rays.append(ray)

            # SWT 后处理
            swt[swt == np.inf] = 0
            swt_norm = cv2.normalize(swt, None, 0, 255, cv2.NORM_MINMAX).astype(np.uint8)
            _, swt_binary = cv2.threshold(swt_norm, 1, 255, cv2.THRESH_BINARY)
            
            # --- 新增：中值滤波平滑SWT图 ---
            swt_binary = cv2.medianBlur(swt_binary, 3)

            num_labels, labels, stats_cc, _ = cv2.connectedComponentsWithStats(swt_binary)

            # --- 新增：简单的字符组件合并 ---
            char_boxes = []
            for i in range(1, num_labels):
                if stats_cc[i, cv2.CC_STAT_AREA] > self.config['connected_component_min_area']:
                    x, y, w, h = stats_cc[i, cv2.CC_STAT_LEFT], stats_cc[i, cv2.CC_STAT_TOP], \
                                 stats_cc[i, cv2.CC_STAT_WIDTH], stats_cc[i, cv2.CC_STAT_HEIGHT]
                    if 0.1 < w/h < 10 and h > 8:
                        char_boxes.append([x, y, x+w, y+h])

            # 水平合并字符框
            def merge_boxes(boxes):
                if not boxes: return []
                boxes.sort(key=lambda b: b[0])
                merged = [boxes[0]]
                for box in boxes[1:]:
                    last = merged[-1]
                    # 如果垂直重叠且水平接近，则合并
                    if (box[1] < last[3] and box[3] > last[1]) and \
                       (box[0] - last[2] < (last[3] - last[1])): # 间距小于高度
                        last[2] = max(last[2], box[2])
                        last[3] = max(last[3], box[3])
                        last[1] = min(last[1], box[1])
                    else:
                        merged.append(box)
                return merged

            merged_box_coords = merge_boxes(char_boxes)
            final_regions = []
            for box in merged_box_coords:
                x1, y1, x2, y2 = box
                final_regions.append(np.array([[x1, y1], [x2, y1], [x2, y2], [x1, y2]], dtype=np.float32))

            return final_regions, {'swt_rays': len(rays)}

        except Exception as e:
            logger.error(f"SWT检测失败: {e}", exc_info=True)
            return [], {'error': str(e)}
    
    def _trace_stroke_width(self, edges: np.ndarray, gradient_direction: np.ndarray, 
                           start_x: int, start_y: int, direction: float, shape: Tuple[int, int]) -> float:
        """追踪笔画宽度"""
        try:
            h, w = shape
            x, y = start_x, start_y
            dx, dy = np.cos(direction), np.sin(direction)
            
            distance = 0
            max_distance = 100  # 最大追踪距离
            
            while distance < max_distance:
                x += dx
                y += dy
                distance += 1
                
                # 检查边界
                if x < 0 or x >= w or y < 0 or y >= h:
                    break
                
                xi, yi = int(round(x)), int(round(y))
                
                # 如果遇到另一个边缘点
                if edges[yi, xi] > 0:
                    # 检查梯度方向是否相反
                    opposite_direction = gradient_direction[yi, xi]
                    angle_diff = abs(direction - opposite_direction)
                    
                    if angle_diff > np.pi / 2 and angle_diff < 3 * np.pi / 2:
                        return distance
            
            return -1  # 未找到匹配的边缘
            
        except Exception:
            return -1
    
    def _validate_stroke_consistency(self, box: np.ndarray, swt: np.ndarray) -> bool:
        """验证笔画宽度一致性"""
        try:
            # 创建区域掩膜
            mask = np.zeros(swt.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [box.astype(np.int32)], 255)
            
            # 提取区域内的笔画宽度值
            region_swt = swt[mask > 0]
            valid_swt = region_swt[region_swt < np.inf]
            
            if len(valid_swt) < 5:  # 太少的有效笔画点
                return False
            
            # 计算笔画宽度的变异系数
            mean_stroke = np.mean(valid_swt)
            std_stroke = np.std(valid_swt)
            
            if mean_stroke == 0:
                return False
            
            cv = std_stroke / mean_stroke
            
            # 笔画宽度应该相对一致
            return cv < 0.8  # 变异系数小于0.8
            
        except Exception:
            return False
    
    def _connected_component_analysis(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """
        连通分量分析 (V2 - 增强版)
        - 增加断裂字符合并逻辑（如合并 'i' 的点和杠）。
        - 增加粘连字符分割的初步尝试（基于形态学）。
        """
        try:
            regions = []
            stats = {'total_components': 0, 'valid_components': 0, 'merged': 0, 'split': 0}
            
            binary_methods = [
                lambda img: cv2.adaptiveThreshold(img, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY_INV, 11, 2),
                lambda img: cv2.threshold(img, 0, 255, cv2.THRESH_BINARY_INV + cv2.THRESH_OTSU)[1]
            ]
            
            all_components = []
            for binary_method in binary_methods:
                try:
                    binary = binary_method(gray)
                    
                    # --- 新增：尝试分割粘连字符 ---
                    # 使用形态学开运算来断开细小的连接
                    kernel = np.ones((3,1), np.uint8)
                    binary_split = cv2.morphologyEx(binary, cv2.MORPH_OPEN, kernel)
                    
                    num_labels, _, stats_cc, centroids = cv2.connectedComponentsWithStats(binary_split, connectivity=8)
                    stats['total_components'] += num_labels - 1
                    
                    for i in range(1, num_labels):
                        area, w, h = stats_cc[i, cv2.CC_STAT_AREA], stats_cc[i, cv2.CC_STAT_WIDTH], stats_cc[i, cv2.CC_STAT_HEIGHT]
                        if (area > self.config['connected_component_min_area'] and 
                            self.config['char_min_width'] <= w <= self.config['char_max_width'] and
                            self.config['char_min_height'] <= h <= self.config['char_max_height']):
                            
                            x, y = stats_cc[i, cv2.CC_STAT_LEFT], stats_cc[i, cv2.CC_STAT_TOP]
                            all_components.append({'bbox': [x, y, x+w, y+h], 'centroid': centroids[i]})
                            stats['valid_components'] += 1

                except Exception as e:
                    logger.warning(f"连通分量方法失败: {e}")
                    continue
            
            # --- 新增：断裂字符合并逻辑 ---
            if not all_components: return [], stats
            
            merged_components = []
            all_components.sort(key=lambda c: (c['bbox'][1], c['bbox'][0])) # 从上到下，从左到右排序
            used = [False] * len(all_components)

            for i in range(len(all_components)):
                if used[i]: continue
                
                comp1 = all_components[i]
                bbox1 = comp1['bbox']
                merged_bbox = list(bbox1)
                
                for j in range(i + 1, len(all_components)):
                    if used[j]: continue
                    comp2 = all_components[j]
                    bbox2 = comp2['bbox']

                    # 检查是否垂直对齐且足够近 (合并 'i' 的点)
                    is_vertically_aligned = abs(comp1['centroid'][0] - comp2['centroid'][0]) < (bbox1[2] - bbox1[0])
                    vertical_gap = bbox2[1] - bbox1[3]
                    is_close = 0 <= vertical_gap < (bbox1[3] - bbox1[1]) * 0.5

                    if is_vertically_aligned and is_close:
                        # 合并bbox
                        merged_bbox[0] = min(merged_bbox[0], bbox2[0])
                        merged_bbox[1] = min(merged_bbox[1], bbox2[1])
                        merged_bbox[2] = max(merged_bbox[2], bbox2[2])
                        merged_bbox[3] = max(merged_bbox[3], bbox2[3])
                        used[j] = True
                        stats['merged'] += 1
                
                merged_components.append(merged_bbox)

            for bbox in merged_components:
                x1, y1, x2, y2 = bbox
                box = np.array([[x1, y1], [x2, y1], [x2, y2], [x1, y2]], dtype=np.float32)
                regions.append(box)

            return regions, stats
            
        except Exception as e:
            logger.error(f"连通分量分析失败: {e}")
            return [], {'error': str(e)}
    
    def _validate_component_shape(self, box: np.ndarray, mask: np.ndarray) -> bool:
        """验证连通分量形状"""
        try:
            # 计算边界框
            x_coords = box[:, 0]
            y_coords = box[:, 1]
            width = np.max(x_coords) - np.min(x_coords)
            height = np.max(y_coords) - np.min(y_coords)
            
            if width <= 0 or height <= 0:
                return False
            
            # 检查宽高比
            aspect_ratio = width / height
            if not (self.config['char_aspect_ratio_min'] <= aspect_ratio <= self.config['char_aspect_ratio_max']):
                return False
            
            # 计算填充比例
            box_area = width * height
            mask_roi = mask[int(np.min(y_coords)):int(np.max(y_coords))+1, 
                           int(np.min(x_coords)):int(np.max(x_coords))+1]
            
            if mask_roi.size == 0:
                return False
            
            filled_pixels = np.sum(mask_roi > 0)
            fill_ratio = filled_pixels / box_area
            
            return fill_ratio >= self.config['min_fill_ratio']
            
        except Exception:
            return False
    
    def _character_level_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """
        字符级检测 (V2 - 增强版)
        - 使用距离变换 + 分水岭算法代替鲁棒性差的垂直投影法。
        - 能够在一定程度上处理倾斜和粘连的字符。
        """
        try:
            stats = {'char_candidates': 0, 'valid_chars': 0}
            
            # 1. 预处理
            binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                           cv2.THRESH_BINARY_INV, 15, 4)
            
            # 移除小的噪声
            kernel = np.ones((2,2), np.uint8)
            opening = cv2.morphologyEx(binary, cv2.MORPH_OPEN, kernel, iterations=2)
            
            # 确定背景区域
            sure_bg = cv2.dilate(opening, kernel, iterations=3)

            # 2. 距离变换
            dist_transform = cv2.distanceTransform(opening, cv2.DIST_L2, 5)
            # 归一化以方便设置阈值
            cv2.normalize(dist_transform, dist_transform, 0, 1.0, cv2.NORM_MINMAX)
            
            # 确定前景区域（字符的核心）
            # 距离变换图中值越大的点，越是字符的中心
            _, sure_fg = cv2.threshold(dist_transform, 0.5 * dist_transform.max(), 255, 0)
            sure_fg = np.uint8(sure_fg)

            # 找到未知区域（可能是字符边界）
            unknown = cv2.subtract(sure_bg, sure_fg)

            # 3. 连通分量标记
            # sure_fg 里的每个连通区域都是一个字符的核心
            num_labels, markers = cv2.connectedComponents(sure_fg)
            # 将背景标记为0
            markers = markers + 1
            # 将未知区域标记为0，这样分水岭算法就会在这里画出边界
            markers[unknown == 255] = 0
            
            # 4. 分水岭算法
            # 分水岭算法需要一个3通道图像
            gray_3channel = cv2.cvtColor(gray, cv2.COLOR_GRAY2BGR)
            markers = cv2.watershed(gray_3channel, markers)

            # 5. 提取分割后的字符区域
            final_regions = []
            for label in np.unique(markers):
                # -1是边界，1是背景
                if label <= 1: continue

                # 创建一个只包含当前字符的掩码
                mask = np.zeros(gray.shape, dtype="uint8")
                mask[markers == label] = 255
                
                # 查找该字符的轮廓
                contours, _ = cv2.findContours(mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                if contours:
                    # 使用最小外接矩形作为边界框
                    contour = max(contours, key=cv2.contourArea)
                    rect = cv2.minAreaRect(contour)
                    box = cv2.boxPoints(rect)
                    
                    if self._validate_character_region(box, gray):
                        final_regions.append(box.astype(np.float32))
                        stats['valid_chars'] += 1

            return final_regions, stats
            
        except Exception as e:
            logger.error(f"字符级检测失败: {e}", exc_info=True)
            return [], {'error': str(e)}
    
    def _separate_characters(self, gray: np.ndarray) -> List[np.ndarray]:
        """分离单个字符"""
        try:
            regions = []
            
            # 自适应阈值
            binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                         cv2.THRESH_BINARY_INV, 11, 2)
            
            # 垂直投影分析
            vertical_projection = np.sum(binary, axis=0)
            
            # 查找字符分界点
            separation_points = []
            in_char = False
            char_start = 0
            
            min_char_width = self.config['char_min_width']
            
            for i, projection in enumerate(vertical_projection):
                if projection > 0 and not in_char:
                    # 字符开始
                    char_start = i
                    in_char = True
                elif projection == 0 and in_char:
                    # 字符结束
                    char_width = i - char_start
                    if char_width >= min_char_width:
                        separation_points.append((char_start, i))
                    in_char = False
            
            # 处理最后一个字符
            if in_char and len(vertical_projection) - char_start >= min_char_width:
                separation_points.append((char_start, len(vertical_projection)))
            
            # 为每个分离的字符创建边界框
            for start_x, end_x in separation_points:
                # 在字符区域内进行水平投影
                char_region = binary[:, start_x:end_x]
                horizontal_projection = np.sum(char_region, axis=1)
                
                # 查找字符的上下边界
                non_zero_rows = np.where(horizontal_projection > 0)[0]
                if len(non_zero_rows) > 0:
                    start_y = non_zero_rows[0]
                    end_y = non_zero_rows[-1] + 1
                    
                    # 创建字符边界框
                    char_box = np.array([
                        [start_x, start_y],
                        [end_x, start_y],
                        [end_x, end_y],
                        [start_x, end_y]
                    ], dtype=np.float32)
                    
                    regions.append(char_box)
            
            return regions
            
        except Exception as e:
            logger.error(f"字符分离失败: {e}")
            return []
    
    def _validate_character_region(self, box: np.ndarray, gray: np.ndarray) -> bool:
        """验证字符区域"""
        try:
            # 计算尺寸
            x_coords = box[:, 0]
            y_coords = box[:, 1]
            width = np.max(x_coords) - np.min(x_coords)
            height = np.max(y_coords) - np.min(y_coords)
            
            # 尺寸检查
            if (width < self.config['char_min_width'] or width > self.config['char_max_width'] or
                height < self.config['char_min_height'] or height > self.config['char_max_height']):
                return False
            
            # 宽高比检查
            aspect_ratio = width / height if height > 0 else 0
            if not (self.config['char_aspect_ratio_min'] <= aspect_ratio <= self.config['char_aspect_ratio_max']):
                return False
            
            # 内容密度检查
            mask = np.zeros(gray.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [box.astype(np.int32)], 255)
            
            # 提取区域
            roi = cv2.bitwise_and(gray, gray, mask=mask)
            non_zero_pixels = np.sum(roi > 0)
            total_pixels = np.sum(mask > 0)
            
            if total_pixels == 0:
                return False
            
            density = non_zero_pixels / total_pixels
            return density >= self.config['min_fill_ratio']
            
        except Exception:
            return False
    def _optimize_text_regions(self, regions: List[np.ndarray], image_shape: Tuple[int, int]) -> List[np.ndarray]:
        """优化文本区域"""
        try:
            if not regions:
                return []
            
            # 1. 基本过滤
            filtered_regions = []
            h, w = image_shape[:2]
            
            for region in regions:
                if self._is_valid_region_geometry(region, (w, h)):
                    filtered_regions.append(region)
            
            # 2. 去重处理
            deduplicated_regions = self._remove_duplicate_regions(filtered_regions)
            
            # 3. 重叠处理
            non_overlapping_regions = self._resolve_overlapping_regions(deduplicated_regions)
            
            # 4. 边界优化
            boundary_optimized = self._optimize_region_boundaries(non_overlapping_regions, image_shape)
            
            return boundary_optimized
            
        except Exception as e:
            logger.error(f"区域优化失败: {e}")
            return regions
    
    def _is_valid_region_geometry(self, region: np.ndarray, image_size: Tuple[int, int]) -> bool:
        """验证区域几何形状"""
        try:
            w, h = image_size
            
            # 计算区域属性
            x_coords = region[:, 0]
            y_coords = region[:, 1]
            
            min_x, max_x = np.min(x_coords), np.max(x_coords)
            min_y, max_y = np.min(y_coords), np.max(y_coords)
            
            width = max_x - min_x
            height = max_y - min_y
            area = width * height
            
            # 基本尺寸检查
            if (width < self.config['min_text_size'] or height < self.config['min_text_size'] or
                width > w * 0.95 or height > h * 0.95):
                return False
            
            # 面积检查
            if area < self.config['min_text_size'] ** 2 or area > (w * h * 0.8):
                return False
            
            # 宽高比检查
            aspect_ratio = width / height if height > 0 else float('inf')
            if aspect_ratio < 0.05 or aspect_ratio > 20:
                return False
            
            # 边界检查
            if min_x < 0 or min_y < 0 or max_x > w or max_y > h:
                return False
            
            return True
            
        except Exception:
            return False
    
    def _remove_duplicate_regions(self, regions: List[np.ndarray]) -> List[np.ndarray]:
        """移除重复区域"""
        try:
            if len(regions) <= 1:
                return regions
            
            unique_regions = []
            
            for i, region1 in enumerate(regions):
                is_duplicate = False
                
                for j, region2 in enumerate(unique_regions):
                    if self._calculate_region_similarity(region1, region2) > 0.9:
                        is_duplicate = True
                        break
                
                if not is_duplicate:
                    unique_regions.append(region1)
            
            return unique_regions
            
        except Exception as e:
            logger.error(f"去重失败: {e}")
            return regions
    
    def _calculate_region_similarity(self, region1: np.ndarray, region2: np.ndarray) -> float:
        """计算区域相似度"""
        try:
            # 计算IoU (Intersection over Union)
            def get_bbox(region):
                x_coords = region[:, 0]
                y_coords = region[:, 1]
                return np.min(x_coords), np.min(y_coords), np.max(x_coords), np.max(y_coords)
            
            x1_min, y1_min, x1_max, y1_max = get_bbox(region1)
            x2_min, y2_min, x2_max, y2_max = get_bbox(region2)
            
            # 计算交集
            intersection_x_min = max(x1_min, x2_min)
            intersection_y_min = max(y1_min, y2_min)
            intersection_x_max = min(x1_max, x2_max)
            intersection_y_max = min(y1_max, y2_max)
            
            if intersection_x_min >= intersection_x_max or intersection_y_min >= intersection_y_max:
                return 0.0
            
            intersection_area = (intersection_x_max - intersection_x_min) * (intersection_y_max - intersection_y_min)
            
            # 计算并集
            area1 = (x1_max - x1_min) * (y1_max - y1_min)
            area2 = (x2_max - x2_min) * (y2_max - y2_min)
            union_area = area1 + area2 - intersection_area
            
            if union_area <= 0:
                return 0.0
            
            return intersection_area / union_area
            
        except Exception:
            return 0.0
    
    def _resolve_overlapping_regions(self, regions: List[np.ndarray]) -> List[np.ndarray]:
        """处理重叠区域"""
        try:
            if len(regions) <= 1:
                return regions
            
            resolved_regions = []
            region_groups = []
            
            # 找到重叠的区域组
            for region in regions:
                added_to_group = False
                
                for group in region_groups:
                    for group_region in group:
                        if self._calculate_region_similarity(region, group_region) > self.config['max_overlap_ratio']:
                            group.append(region)
                            added_to_group = True
                            break
                    if added_to_group:
                        break
                
                if not added_to_group:
                    region_groups.append([region])
            
            # 处理每个组
            for group in region_groups:
                if len(group) == 1:
                    resolved_regions.append(group[0])
                else:
                    # 合并重叠区域
                    merged_region = self._merge_region_group(group)
                    if merged_region is not None:
                        resolved_regions.append(merged_region)
            
            return resolved_regions
            
        except Exception as e:
            logger.error(f"重叠区域处理失败: {e}")
            return regions
    
    def _merge_region_group(self, regions: List[np.ndarray]) -> Optional[np.ndarray]:
        """合并区域组"""
        try:
            if not regions:
                return None
            
            if len(regions) == 1:
                return regions[0]
            
            # 计算所有区域的边界
            all_x_coords = []
            all_y_coords = []
            
            for region in regions:
                all_x_coords.extend(region[:, 0])
                all_y_coords.extend(region[:, 1])
            
            # 创建合并后的边界框
            min_x, max_x = np.min(all_x_coords), np.max(all_x_coords)
            min_y, max_y = np.min(all_y_coords), np.max(all_y_coords)
            
            merged_region = np.array([
                [min_x, min_y],
                [max_x, min_y],
                [max_x, max_y],
                [min_x, max_y]
            ], dtype=np.float32)
            
            return merged_region
            
        except Exception:
            return None
    
    def _optimize_region_boundaries(self, regions: List[np.ndarray], image_shape: Tuple[int, int]) -> List[np.ndarray]:
        """优化区域边界"""
        try:
            optimized_regions = []
            h, w = image_shape[:2]
            
            for region in regions:
                # 添加边距
                margin = self.config['add_margin']
                
                x_coords = region[:, 0]
                y_coords = region[:, 1]
                
                # 计算当前边界
                min_x, max_x = np.min(x_coords), np.max(x_coords)
                min_y, max_y = np.min(y_coords), np.max(y_coords)
                
                width = max_x - min_x
                height = max_y - min_y
                
                # 添加自适应边距
                x_margin = width * margin
                y_margin = height * margin
                
                # 应用边距并确保在图像边界内
                new_min_x = max(0, min_x - x_margin)
                new_max_x = min(w, max_x + x_margin)
                new_min_y = max(0, min_y - y_margin)
                new_max_y = min(h, max_y + y_margin)
                
                # 创建优化后的区域
                optimized_region = np.array([
                    [new_min_x, new_min_y],
                    [new_max_x, new_min_y],
                    [new_max_x, new_max_y],
                    [new_min_x, new_max_y]
                ], dtype=np.float32)
                
                optimized_regions.append(optimized_region)
            
            return optimized_regions
            
        except Exception as e:
            logger.error(f"边界优化失败: {e}")
            return regions
    
    def _reorganize_text_lines(self, regions: List[np.ndarray], gray: np.ndarray) -> List[np.ndarray]:
        """重组文本行"""
        try:
            if not regions:
                return []
            
            # 1. 按Y坐标排序区域
            regions_with_y = [(region, np.mean(region[:, 1])) for region in regions]
            regions_with_y.sort(key=lambda x: x[1])
            
            # 2. 分组相近的Y坐标区域
            line_groups = []
            current_group = []
            current_y = None
            
            height_threshold = self.config['text_line_merge_distance']
            
            for region, y_coord in regions_with_y:
                if current_y is None or abs(y_coord - current_y) <= height_threshold:
                    current_group.append(region)
                    current_y = y_coord if current_y is None else (current_y + y_coord) / 2
                else:
                    if current_group:
                        line_groups.append(current_group)
                    current_group = [region]
                    current_y = y_coord
            
            if current_group:
                line_groups.append(current_group)
            
            # 3. 处理每个行组
            reorganized_lines = []
            
            for group in line_groups:
                if len(group) == 1:
                    reorganized_lines.append(group[0])
                else:
                    # 检查是否应该合并为一行
                    if self._should_merge_as_text_line(group, gray):
                        merged_line = self._merge_text_line(group)
                        if merged_line is not None:
                            reorganized_lines.append(merged_line)
                    else:
                        # 作为独立区域保留
                        reorganized_lines.extend(group)
            
            return reorganized_lines
            
        except Exception as e:
            logger.error(f"文本行重组失败: {e}")
            return regions
    
    def _should_merge_as_text_line(self, regions: List[np.ndarray], gray: np.ndarray) -> bool:
        """判断是否应该合并为文本行"""
        try:
            if len(regions) < 2:
                return False
            
            # 计算区域间的水平距离
            regions_with_x = [(region, np.mean(region[:, 0])) for region in regions]
            regions_with_x.sort(key=lambda x: x[1])
            
            # 检查间距是否合理
            distances = []
            for i in range(len(regions_with_x) - 1):
                region1, x1 = regions_with_x[i]
                region2, x2 = regions_with_x[i + 1]
                
                # 计算区域右边界到下一个区域左边界的距离
                right_x1 = np.max(region1[:, 0])
                left_x2 = np.min(region2[:, 0])
                distance = left_x2 - right_x1
                distances.append(distance)
            
            # 检查距离是否在合理范围内
            if not distances:
                return False
            
            max_reasonable_distance = 50  # 可调整的参数
            return all(0 <= d <= max_reasonable_distance for d in distances)
            
        except Exception:
            return False
    
    def _merge_text_line(self, regions: List[np.ndarray]) -> Optional[np.ndarray]:
        """合并文本行"""
        try:
            if not regions:
                return None
            
            # 计算合并边界
            all_x_coords = []
            all_y_coords = []
            
            for region in regions:
                all_x_coords.extend(region[:, 0])
                all_y_coords.extend(region[:, 1])
            
            min_x, max_x = np.min(all_x_coords), np.max(all_x_coords)
            min_y, max_y = np.min(all_y_coords), np.max(all_y_coords)
            
            # 创建合并后的文本行
            merged_line = np.array([
                [min_x, min_y],
                [max_x, min_y],
                [max_x, max_y],
                [min_x, max_y]
            ], dtype=np.float32)
            
            return merged_line
            
        except Exception:
            return None
    
    def _manage_segmentation_cache(self, cache_key: str, result: Dict):
        """管理分割缓存"""
        try:
            if len(self._segmentation_cache) >= self._cache_max_size:
                # 删除最旧的缓存条目
                oldest_key = next(iter(self._segmentation_cache))
                del self._segmentation_cache[oldest_key]
            
            self._segmentation_cache[cache_key] = result
            
        except Exception as e:
            logger.error(f"分割缓存管理失败: {e}")
    
    def clear_segmentation_cache(self):
        """清理分割缓存"""
        try:
            self._segmentation_cache.clear()
            logger.info("文本分割缓存已清理")
        except Exception as e:
            logger.error(f"清理分割缓存失败: {e}")
    
    def get_segmentation_stats(self) -> Dict:
        """获取分割统计信息"""
        return {
            'cache_size': len(self._segmentation_cache),
            'max_cache_size': self._cache_max_size,
            'config': self.config.copy()
        }
    
    # 新增高级分割方法
    def _multilevel_mser_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """
        多层次MSER检测 (V3 - API兼容最终版)
        - 同样采用创建实例后逐一设置参数的方式，解决兼容性问题。
        """
        try:
            all_regions_with_scores_levels = []
            stats = {'levels_processed': 0, 'raw_regions_per_level': []}

            # 现在 config 字典中的键名是什么已不再重要，因为我们将通过 setter 调用
            mser_levels_configs = [
                {'delta': 3, 'min_area': 15, 'max_area': 2000, 'max_variation': 0.15, 'min_diversity': 0.3},
                {'delta': 5, 'min_area': 50, 'max_area': 8000, 'max_variation': 0.25, 'min_diversity': 0.2},
                {'delta': 7, 'min_area': 150, 'max_area': 15000, 'max_variation': 0.35, 'min_diversity': 0.15},
            ]
            
            for level, config in enumerate(mser_levels_configs):
                level_regions_scores = []
                for image_pass in [gray, cv2.bitwise_not(gray)]:
                    try:
                        # --- 核心修正：采用 Setter 方法配置 MSER ---
                        mser = cv2.MSER_create()
                        mser.setDelta(config['delta'])
                        mser.setMinArea(config['min_area'])
                        mser.setMaxArea(config['max_area'])
                        mser.setMaxVariation(config['max_variation'])
                        mser.setMinDiversity(config['min_diversity'])
                        # --- 修正结束 ---

                        level_regions, _ = mser.detectRegions(image_pass)
                        
                        for region in level_regions:
                            hull = cv2.convexHull(region.reshape(-1, 1, 2))
                            rect = cv2.minAreaRect(hull)
                            box = cv2.boxPoints(rect)
                            
                            if self._validate_multilevel_region(box, gray, level):
                                score = cv2.contourArea(box)
                                level_regions_scores.append((box, score, level))

                    except Exception as e:
                        logger.warning(f"MSER级别{level}失败: {e}")
                
                stats['raw_regions_per_level'].append(len(level_regions_scores))
                all_regions_with_scores_levels.extend(level_regions_scores)
                stats['levels_processed'] += 1
            
            if not all_regions_with_scores_levels:
                return [], stats

            boxes = [item[0] for item in all_regions_with_scores_levels]
            scores = [item[1] for item in all_regions_with_scores_levels]
            rects_for_nms = [cv2.boundingRect(box.astype(np.int32)) for box in boxes]
            
            indices = cv2.dnn.NMSBoxes(rects_for_nms, scores, score_threshold=0.1, nms_threshold=0.4)
            
            final_regions = []
            if len(indices) > 0:
                for i in indices.flatten():
                    final_regions.append(boxes[i].astype(np.float32))

            return final_regions, stats
            
        except Exception as e:
            logger.error(f"多层次MSER检测失败: {e}")
            return [], {'error': str(e)}
    
    def _validate_multilevel_region(self, box: np.ndarray, gray: np.ndarray, level: int) -> bool:
        """多层次区域验证"""
        try:
            # 基本几何验证
            if not self._validate_text_region(box, gray):
                return False
            
            # 根据层次进行不同的验证
            x_coords = box[:, 0]
            y_coords = box[:, 1]
            width = np.max(x_coords) - np.min(x_coords)
            height = np.max(y_coords) - np.min(y_coords)
            
            # 层次特定的尺寸要求
            if level == 0:  # 细粒度 - 字符级
                return (4 <= width <= 80 and 8 <= height <= 120)
            elif level == 1:  # 中等粒度 - 词语级
                return (20 <= width <= 200 and 10 <= height <= 150)
            elif level == 2:  # 粗粒度 - 短句级
                return (50 <= width <= 400 and 15 <= height <= 100)
            else:  # 超大区域 - 段落级
                return (100 <= width <= 800 and 20 <= height <= 200)
            
        except Exception:
            return False
    
    def _adaptive_multithreshold_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """自适应多阈值检测"""
        try:
            regions = []
            stats = {'thresholds_used': [], 'regions_per_threshold': []}
            
            # 自适应确定阈值范围
            mean_intensity = np.mean(gray)
            std_intensity = np.std(gray)
            
            # 动态生成阈值
            base_thresholds = [
                mean_intensity - 2 * std_intensity,
                mean_intensity - std_intensity,
                mean_intensity,
                mean_intensity + std_intensity,
                mean_intensity + 2 * std_intensity
            ]
            
            # 确保阈值在有效范围内
            thresholds = [max(0, min(255, t)) for t in base_thresholds]
            thresholds = sorted(list(set(thresholds)))  # 去重并排序
            
            for threshold in thresholds:
                try:
                    # 固定阈值二值化
                    _, binary = cv2.threshold(gray, threshold, 255, cv2.THRESH_BINARY_INV)
                    
                    # 多种形态学操作
                    morphology_configs = [
                        (cv2.MORPH_RECT, (2, 1)),
                        (cv2.MORPH_RECT, (1, 2)),
                        (cv2.MORPH_RECT, (3, 3)),
                        (cv2.MORPH_ELLIPSE, (3, 3))
                    ]
                    
                    threshold_regions = []
                    
                    for morph_type, kernel_size in morphology_configs:
                        kernel = cv2.getStructuringElement(morph_type, kernel_size)
                        processed = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel)
                        
                        # 查找轮廓
                        contours, _ = cv2.findContours(processed, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                        
                        for contour in contours:
                            area = cv2.contourArea(contour)
                            if area > self.config['connected_component_min_area']:
                                rect = cv2.minAreaRect(contour)
                                box = cv2.boxPoints(rect)
                                
                                if self._validate_threshold_region(box, binary):
                                    threshold_regions.append(box.astype(np.float32))
                    
                    regions.extend(threshold_regions)
                    stats['thresholds_used'].append(threshold)
                    stats['regions_per_threshold'].append(len(threshold_regions))
                    
                except Exception as e:
                    logger.warning(f"阈值{threshold}处理失败: {e}")
                    continue
            
            return regions, stats
            
        except Exception as e:
            logger.error(f"自适应多阈值检测失败: {e}")
            return [], {'error': str(e)}
    
    def _validate_threshold_region(self, box: np.ndarray, binary: np.ndarray) -> bool:
        """验证阈值区域"""
        try:
            # 创建区域掩膜
            mask = np.zeros(binary.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [box.astype(np.int32)], 255)
            
            # 计算区域内的前景像素比例
            region_pixels = cv2.bitwise_and(binary, binary, mask=mask)
            foreground_pixels = np.sum(region_pixels > 0)
            total_pixels = np.sum(mask > 0)
            
            if total_pixels == 0:
                return False
            
            fill_ratio = foreground_pixels / total_pixels
            
            # 阈值区域应该有适当的填充比例
            return 0.1 <= fill_ratio <= 0.9
            
        except Exception:
            return False
    
    def _orientation_adaptive_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """方向自适应检测"""
        try:
            regions = []
            stats = {'orientations_tested': [], 'regions_per_orientation': []}
            
            # 检测主要文本方向
            dominant_angles = self._detect_dominant_text_orientations(gray)
            
            for angle in dominant_angles:
                try:
                    # 旋转图像到水平方向
                    if abs(angle) > 1:  # 只有角度足够大时才旋转
                        center = (gray.shape[1] // 2, gray.shape[0] // 2)
                        rotation_matrix = cv2.getRotationMatrix2D(center, angle, 1.0)
                        rotated_gray = cv2.warpAffine(gray, rotation_matrix, (gray.shape[1], gray.shape[0]),
                                                    flags=cv2.INTER_LINEAR, borderMode=cv2.BORDER_CONSTANT, borderValue=255)
                    else:
                        rotated_gray = gray
                    
                    # 在旋转后的图像上进行文本检测
                    orientation_regions = self._detect_horizontal_text_regions(rotated_gray)
                    
                    # 将检测到的区域旋转回原始方向
                    if abs(angle) > 1:
                        inverse_rotation_matrix = cv2.getRotationMatrix2D(center, -angle, 1.0)
                        for i, region in enumerate(orientation_regions):
                            # 旋转区域坐标
                            ones = np.ones(shape=(len(region), 1))
                            points_ones = np.hstack([region, ones])
                            transformed_points = inverse_rotation_matrix.dot(points_ones.T).T
                            orientation_regions[i] = transformed_points.astype(np.float32)
                    
                    regions.extend(orientation_regions)
                    stats['orientations_tested'].append(angle)
                    stats['regions_per_orientation'].append(len(orientation_regions))
                    
                except Exception as e:
                    logger.warning(f"方向{angle}度检测失败: {e}")
                    continue
            
            return regions, stats
            
        except Exception as e:
            logger.error(f"方向自适应检测失败: {e}")
            return [], {'error': str(e)}
    
    def _detect_dominant_text_orientations(self, gray: np.ndarray) -> List[float]:
        """检测主要文本方向"""
        try:
            # 使用霍夫变换检测直线
            edges = cv2.Canny(gray, 50, 150, apertureSize=3)
            lines = cv2.HoughLines(edges, 1, np.pi/180, threshold=100)
            
            angles = []
            if lines is not None:
                for line in lines:
                    rho, theta = line[0]
                    angle = np.degrees(theta - np.pi/2)  # 转换为文本角度
                    angles.append(angle)
            
            # 角度聚类
            if not angles:
                return [0.0]  # 默认水平方向
            
            # 简单的角度聚类
            angle_bins = {}
            bin_size = 5  # 5度为一个区间
            
            for angle in angles:
                bin_key = round(angle / bin_size) * bin_size
                bin_key = bin_key % 180  # 规范化到0-180度
                if bin_key > 90:
                    bin_key = bin_key - 180  # 转换到-90到90度范围
                
                if bin_key not in angle_bins:
                    angle_bins[bin_key] = 0
                angle_bins[bin_key] += 1
            
            # 选择最频繁的方向
            if angle_bins:
                dominant_angles = sorted(angle_bins.keys(), key=lambda x: angle_bins[x], reverse=True)
                return dominant_angles[:3]  # 返回前3个主要方向
            else:
                return [0.0]
            
        except Exception as e:
            logger.warning(f"主要方向检测失败: {e}")
            return [0.0]
    
    def _detect_horizontal_text_regions(self, gray: np.ndarray) -> List[np.ndarray]:
        """
        检测水平文本区域。
        此方法专门优化用于检测横向排列的文本行。
        它使用自适应阈值和水平方向的形态学操作来连接字符，
        然后提取轮廓并根据宽高比进行过滤。
        """
        try:
            regions = []

            # 针对水平文本优化的形态学操作
            # 修正：将所有 'cv.' 替换为 'cv2.'
            binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                           cv2.THRESH_BINARY_INV, 11, 2)

            # 水平连接核，用于连接同一行内的字符
            horizontal_kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (10, 1))
            # 闭运算连接断裂的文本部分
            horizontal_lines = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, horizontal_kernel)

            # 查找水平文本区域的轮廓
            contours, _ = cv2.findContours(horizontal_lines, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)

            for contour in contours:
                area = cv2.contourArea(contour)
                # 过滤掉过小的噪声区域
                if area > self.config['min_text_size'] ** 2:
                    # 获取边界矩形
                    x, y, w, h = cv2.boundingRect(contour)

                    # 验证是否为水平文本：宽度远大于高度
                    aspect_ratio = w / h if h > 0 else 0
                    if aspect_ratio > 1.5:  # 水平文本的宽高比通常大于1.5
                        box = np.array([
                            [x, y],
                            [x + w, y],
                            [x + w, y + h],
                            [x, y + h]
                        ], dtype=np.float32)
                        regions.append(box)
            
            return regions

        except Exception as e:
            # 捕获任何潜在错误并记录，返回空列表
            logger.error(f"水平文本检测失败: {e}")
            return []     
    def _ultra_precise_merging(self, regions: List[np.ndarray], gray: np.ndarray) -> List[np.ndarray]:
        """超精确合并"""
        try:
            if not regions:
                return []
            
            # 基于多种相似度度量的智能合并
            merged_regions = []
            region_groups = []
            
            # 计算所有区域对的相似度
            similarity_matrix = np.zeros((len(regions), len(regions)))
            
            for i, region1 in enumerate(regions):
                for j, region2 in enumerate(regions):
                    if i != j:
                        # 综合相似度评分
                        geo_sim = self._calculate_geometric_similarity(region1, region2)
                        spatial_sim = self._calculate_spatial_similarity(region1, region2)
                        content_sim = self._calculate_content_similarity(region1, region2, gray)
                        
                        # 加权平均
                        total_sim = (geo_sim * 0.3 + spatial_sim * 0.4 + content_sim * 0.3)
                        similarity_matrix[i, j] = total_sim
            
            # 基于相似度矩阵进行聚类
            visited = [False] * len(regions)
            
            for i in range(len(regions)):
                if visited[i]:
                    continue
                
                group = [i]
                visited[i] = True
                
                # 找到相似的区域
                for j in range(len(regions)):
                    if not visited[j] and similarity_matrix[i, j] > self.config['merge_threshold']:
                        group.append(j)
                        visited[j] = True
                
                # 合并组内区域
                if len(group) == 1:
                    merged_regions.append(regions[group[0]])
                else:
                    group_regions = [regions[idx] for idx in group]
                    merged_region = self._intelligent_merge_group(group_regions, gray)
                    if merged_region is not None:
                        merged_regions.append(merged_region)
            
            return merged_regions
            
        except Exception as e:
            logger.error(f"超精确合并失败: {e}")
            return regions
    
    def _calculate_geometric_similarity(self, region1: np.ndarray, region2: np.ndarray) -> float:
        """计算几何相似度"""
        try:
            # 计算尺寸相似度
            def get_dimensions(region):
                x_coords = region[:, 0]
                y_coords = region[:, 1]
                width = np.max(x_coords) - np.min(x_coords)
                height = np.max(y_coords) - np.min(y_coords)
                return width, height
            
            w1, h1 = get_dimensions(region1)
            w2, h2 = get_dimensions(region2)
            
            if w1 <= 0 or h1 <= 0 or w2 <= 0 or h2 <= 0:
                return 0.0
            
            # 尺寸比例相似度
            width_ratio = min(w1, w2) / max(w1, w2)
            height_ratio = min(h1, h2) / max(h1, h2)
            
            # 面积相似度
            area1, area2 = w1 * h1, w2 * h2
            area_ratio = min(area1, area2) / max(area1, area2)
            
            # 宽高比相似度
            aspect1, aspect2 = w1 / h1, w2 / h2
            aspect_ratio = min(aspect1, aspect2) / max(aspect1, aspect2)
            
            return (width_ratio + height_ratio + area_ratio + aspect_ratio) / 4
            
        except Exception:
            return 0.0
    
    def _calculate_spatial_similarity(self, region1: np.ndarray, region2: np.ndarray) -> float:
        """计算空间相似度"""
        try:
            # 计算区域中心点
            center1 = np.mean(region1, axis=0)
            center2 = np.mean(region2, axis=0)
            
            # 计算距离
            distance = np.linalg.norm(center1 - center2)
            
            # 计算区域尺寸
            def get_max_dimension(region):
                x_coords = region[:, 0]
                y_coords = region[:, 1]
                width = np.max(x_coords) - np.min(x_coords)
                height = np.max(y_coords) - np.min(y_coords)
                return max(width, height)
            
            max_dim1 = get_max_dimension(region1)
            max_dim2 = get_max_dimension(region2)
            max_dim = max(max_dim1, max_dim2)
            
            if max_dim <= 0:
                return 0.0
            
            # 归一化距离（距离越小，相似度越高）
            normalized_distance = distance / max_dim
            spatial_similarity = max(0, 1 - normalized_distance)
            
            return spatial_similarity
            
        except Exception:
            return 0.0
    
    def _calculate_content_similarity(self, region1: np.ndarray, region2: np.ndarray, gray: np.ndarray) -> float:
        """计算内容相似度"""
        try:
            # 提取区域内容
            def extract_region_content(region, image):
                mask = np.zeros(image.shape, dtype=np.uint8)
                cv2.fillPoly(mask, [region.astype(np.int32)], 255)
                
                # 计算直方图
                hist = cv2.calcHist([image], [0], mask, [32], [0, 256])
                hist = cv2.normalize(hist, hist).flatten()
                
                # 计算梯度特征
                roi = cv2.bitwise_and(image, image, mask=mask)
                grad_x = cv2.Sobel(roi, cv2.CV_64F, 1, 0, ksize=3)
                grad_y = cv2.Sobel(roi, cv2.CV_64F, 0, 1, ksize=3)
                grad_mag = np.sqrt(grad_x**2 + grad_y**2)
                
                # 梯度统计
                grad_mean = np.mean(grad_mag[mask > 0]) if np.sum(mask > 0) > 0 else 0
                grad_std = np.std(grad_mag[mask > 0]) if np.sum(mask > 0) > 0 else 0
                
                return hist, grad_mean, grad_std
            
            hist1, grad_mean1, grad_std1 = extract_region_content(region1, gray)
            hist2, grad_mean2, grad_std2 = extract_region_content(region2, gray)
            
            # 直方图相似度（使用相关系数）
            hist_similarity = cv2.compareHist(hist1, hist2, cv2.HISTCMP_CORREL)
            
            # 梯度特征相似度
            grad_mean_sim = 1 - abs(grad_mean1 - grad_mean2) / (max(grad_mean1, grad_mean2) + 1e-8)
            grad_std_sim = 1 - abs(grad_std1 - grad_std2) / (max(grad_std1, grad_std2) + 1e-8)
            
            # 综合内容相似度
            content_similarity = (hist_similarity + grad_mean_sim + grad_std_sim) / 3
            return max(0, content_similarity)
            
        except Exception:
            return 0.0
    
    def _intelligent_merge_group(self, regions: List[np.ndarray], gray: np.ndarray) -> Optional[np.ndarray]:
        """智能合并区域组"""
        try:
            if not regions:
                return None
            
            if len(regions) == 1:
                return regions[0]
            
            # 计算最佳合并边界
            all_points = np.vstack(regions)
            
            # 使用凸包获得更好的边界
            hull = cv2.convexHull(all_points)
            
            # 如果凸包点太少，使用边界框
            if len(hull) < 4:
                x_coords = all_points[:, 0]
                y_coords = all_points[:, 1]
                min_x, max_x = np.min(x_coords), np.max(x_coords)
                min_y, max_y = np.min(y_coords), np.max(y_coords)
                
                merged_region = np.array([
                    [min_x, min_y],
                    [max_x, min_y],
                    [max_x, max_y],
                    [min_x, max_y]
                ], dtype=np.float32)
            else:
                # 简化凸包到四个主要点
                merged_region = self._simplify_hull_to_rectangle(hull)
            
            return merged_region
            
        except Exception:
            return None
    
    def _simplify_hull_to_rectangle(self, hull: np.ndarray) -> np.ndarray:
        """将凸包简化为矩形"""
        try:
            # 找到最小外接矩形
            rect = cv2.minAreaRect(hull)
            box = cv2.boxPoints(rect)
            return box.astype(np.float32)
            
        except Exception:
            # 如果失败，返回边界框
            x_coords = hull[:, 0, 0]
            y_coords = hull[:, 0, 1]
            min_x, max_x = np.min(x_coords), np.max(x_coords)
            min_y, max_y = np.min(y_coords), np.max(y_coords)
            
            return np.array([
                [min_x, min_y],
                [max_x, min_y],
                [max_x, max_y],
                [min_x, max_y]
            ], dtype=np.float32)
    
    def _final_optimization(self, regions: List[np.ndarray], gray: np.ndarray) -> List[np.ndarray]:
        """最终优化"""
        try:
            if not regions:
                return []
            
            optimized_regions = []
            
            for region in regions:
                # 多重优化
                optimized_region = self._optimize_single_region(region, gray)
                
                # 最终验证
                if self._final_region_validation(optimized_region, gray):
                    optimized_regions.append(optimized_region)
            
            # 最终排序（按阅读顺序）
            return self._sort_regions_by_reading_order(optimized_regions)
            
        except Exception as e:
            logger.error(f"最终优化失败: {e}")
            return regions
    
    def _optimize_single_region(self, region: np.ndarray, gray: np.ndarray) -> np.ndarray:
        """优化单个区域"""
        try:
            # 边界紧缩优化
            optimized_region = self._tight_boundary_optimization(region, gray)
            
            # 角度微调
            optimized_region = self._fine_tune_rotation(optimized_region, gray)
            
            return optimized_region
            
        except Exception:
            return region
    
    def _tight_boundary_optimization(self, region: np.ndarray, gray: np.ndarray) -> np.ndarray:
        """紧缩边界优化"""
        try:
            # 创建掩膜
            mask = np.zeros(gray.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [region.astype(np.int32)], 255)
            
            # 查找实际内容边界
            coords = np.where(mask > 0)
            if len(coords[0]) == 0:
                return region
            
            min_y, max_y = np.min(coords[0]), np.max(coords[0])
            min_x, max_x = np.min(coords[1]), np.max(coords[1])
            
            # 添加小的边距
            margin = 2
            min_x = max(0, min_x - margin)
            min_y = max(0, min_y - margin)
            max_x = min(gray.shape[1], max_x + margin)
            max_y = min(gray.shape[0], max_y + margin)
            
            tight_region = np.array([
                [min_x, min_y],
                [max_x, min_y],
                [max_x, max_y],
                [min_x, max_y]
            ], dtype=np.float32)
            
            return tight_region
            
        except Exception:
            return region
    
    def _fine_tune_rotation(self, region: np.ndarray, gray: np.ndarray) -> np.ndarray:
        """微调旋转角度"""
        try:
            # 提取区域内容
            mask = np.zeros(gray.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [region.astype(np.int32)], 255)
            
            # 查找文本轮廓
            roi = cv2.bitwise_and(gray, gray, mask=mask)
            binary = cv2.adaptiveThreshold(roi, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                         cv2.THRESH_BINARY_INV, 11, 2)
            
            contours, _ = cv2.findContours(binary, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            
            if not contours:
                return region
            
            # 找到最大轮廓
            largest_contour = max(contours, key=cv2.contourArea)
            
            # 计算最小面积矩形
            rect = cv2.minAreaRect(largest_contour)
            fine_tuned_box = cv2.boxPoints(rect)
            
            return fine_tuned_box.astype(np.float32)
            
        except Exception:
            return region
    
    def _final_region_validation(self, region: np.ndarray, gray: np.ndarray) -> bool:
        """最终区域验证"""
        try:
            # 几何验证
            if not self._validate_text_region(region, gray):
                return False
            
            # 内容密度验证
            mask = np.zeros(gray.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [region.astype(np.int32)], 255)
            
            roi = cv2.bitwise_and(gray, gray, mask=mask)
            
            # 计算变异系数
            roi_pixels = roi[mask > 0]
            if len(roi_pixels) == 0:
                return False
            
            mean_intensity = np.mean(roi_pixels)
            std_intensity = np.std(roi_pixels)
            
            if mean_intensity == 0:
                return False
            
            cv = std_intensity / mean_intensity
            
            # 文本区域应该有适当的变异
            return 0.1 <= cv <= 2.0
            
        except Exception:
            return False
    
    def _sort_regions_by_reading_order(self, regions: List[np.ndarray]) -> List[np.ndarray]:
        """按阅读顺序排序区域"""
        try:
            if not regions:
                return []
            
            # 计算每个区域的中心点和边界
            region_info = []
            for region in regions:
                center = np.mean(region, axis=0)
                y_min = np.min(region[:, 1])
                region_info.append((region, center, y_min))
            
            # 按行排序（首先按Y坐标分组，然后按X坐标排序）
            region_info.sort(key=lambda x: (x[2], x[1][0]))
            
            return [info[0] for info in region_info]
            
        except Exception as e:
            logger.error(f"阅读顺序排序失败: {e}")
            return regions
    
    # 添加一些辅助验证方法
    def _validate_text_region(self, box: np.ndarray, gray: np.ndarray) -> bool:
        """验证文本区域 - 基础验证方法"""
        try:
            # 基本几何检查
            x_coords = box[:, 0]
            y_coords = box[:, 1]
            width = np.max(x_coords) - np.min(x_coords)
            height = np.max(y_coords) - np.min(y_coords)
            
            # 尺寸检查
            if (width < self.config['min_text_size'] or height < self.config['min_text_size'] or
                width > self.config['max_text_size'] or height > self.config['max_text_size']):
                return False
            
            # 宽高比检查
            if height > 0:
                aspect_ratio = width / height
                if aspect_ratio < 0.05 or aspect_ratio > 20:
                    return False
            
            return True
            
        except Exception:
            return False
    
    def _validate_gradient_region(self, box: np.ndarray, magnitude: np.ndarray) -> bool:
        """验证梯度区域"""
        try:
            # 创建掩膜
            mask = np.zeros(magnitude.shape, dtype=np.uint8)
            cv2.fillPoly(mask, [box.astype(np.int32)], 255)
            
            # 计算区域内梯度强度
            region_magnitude = magnitude[mask > 0]
            if len(region_magnitude) == 0:
                return False
            
            mean_magnitude = np.mean(region_magnitude)
            
            # 文本区域应该有足够的梯度强度
            return mean_magnitude > 20  # 阈值可调
            
        except Exception:
            return False



class PPOCRv3TextDetector:
    """
    使用OpenCV DNN模块和PP-OCRv3模型的现代文本检测器。
    这是当前OpenCV Zoo中官方支持的稳定方案。
    """
    def __init__(self, model_name="text_detection_cn_ppocrv3_2023may.onnx", threshold=0.3, nms_threshold=0.4):
        # 直接使用传入的模型文件名
        self.model_name = model_name
            
        self.threshold = threshold
        self.nms_threshold = nms_threshold
        self.net = None
        self.input_size = (736, 736)
        self._initialize_model()

    def _download_model(self, model_path, url):
        """下载PP-OCRv3模型文件"""
        if requests is None:
            logger.error("❌ PP-OCRv3模型下载失败：'requests'库未安装。")
            return False
        try:
            logger.info(f"PP-OCRv3模型文件 '{model_path}' 不存在，正在从官方源下载...")
            with requests.get(url, stream=True, timeout=300) as r:
                r.raise_for_status()
                with open(model_path, 'wb') as f:
                    shutil.copyfileobj(r.raw, f)
            logger.info(f"✅ PP-OCRv3模型下载成功，已保存至: {model_path}")
            return True
        except Exception as e:
            logger.error(f"❌ PP-OCRv3模型下载失败: {e}", exc_info=True)
            if os.path.exists(model_path):
                os.remove(model_path)
            return False

    def _initialize_model(self):
        """初始化模型，如果不存在则下载"""
        model_url = f"https://raw.githubusercontent.com/opencv/opencv_zoo/main/models/text_detection_ppocr/{self.model_name}"
        
        if not os.path.exists(self.model_name):
            if not self._download_model(self.model_name, model_url):
                error_message = (
                    "PP-OCRv3 文本检测模型自动下载失败！\n\n"
                    "这将导致高级文本分割功能无法使用。\n\n"
                    "请手动从以下地址下载模型：\n"
                    f"{model_url}\n\n"
                    f"然后将 '{self.model_name}' 文件放置于程序运行目录下，并重启程序。"
                )
                logger.error(error_message)
                try:
                    messagebox.showerror("关键模型下载失败", error_message)
                except Exception:
                    pass
                return

        try:
            self.net = cv2.dnn.readNet(self.model_name)
            logger.info(f"✅ PP-OCRv3文本检测模型 '{self.model_name}' 加载成功。")
        except Exception as e:
            logger.error(f"❌ 加载PP-OCRv3模型失败: {e}", exc_info=True)
            self.net = None

    def detect_text_regions_advanced(self, image: np.ndarray, 
                                 enabled_algorithms: Optional[List[str]] = None) -> Tuple[List[np.ndarray], Dict]:
        """
        使用PP-OCRv3进行高级文本区域检测。
        """
        if self.net is None:
            logger.error("PP-OCRv3模型未加载，无法进行文本检测。")
            return [], {'error': 'PP-OCRv3 model not loaded'}

        start_time = time.time()
        
        original_height, original_width = image.shape[:2]
        
        blob = cv2.dnn.blobFromImage(image, scalefactor=1.0/255.0, size=self.input_size, mean=(122.67891434, 116.66876762, 104.00698793), swapRB=True, crop=False)
        self.net.setInput(blob)
        
        # --- 关键修正：正确处理多输出模型 ---
        # .forward() 对于多输出模型返回一个元组或列表
        outputs = self.net.forward()

        # 根据PP-OCRv3的结构，第一个输出是scores，第二个是geometry
        # 它们的形状通常是 (N, C, H, W)，我们需要去掉多余的批处理(N)和通道(C)维度
        scores = outputs[0].squeeze()   # squeeze() 会移除所有大小为1的维度
        geometry = outputs[1].squeeze() # 例如 (1, 5, H, W) -> (5, H, W)
        
        if scores.ndim != 2 or geometry.ndim != 3 or geometry.shape[0] != 5:
            error_msg = f"Unexpected output shapes after squeeze. Scores: {scores.shape}, Geometry: {geometry.shape}"
            logger.error(error_msg)
            return [], {'error': error_msg}
        # --- 修正结束 ---

        rects, confidences = self._decode_predictions(scores, geometry)
        
        indices = cv2.dnn.NMSBoxesRotated(rects, confidences, self.threshold, self.nms_threshold)
        
        final_regions = []
        if len(indices) > 0:
            scale_x = original_width / self.input_size[0]
            scale_y = original_height / self.input_size[1]
            for i in indices:
                rot_rect = rects[i]
                # 调整旋转矩形的中心点和大小以匹配原始图像尺寸
                (cx, cy), (w, h), angle = rot_rect
                orig_cx, orig_cy = cx * scale_x, cy * scale_y
                orig_w, orig_h = w * scale_x, h * scale_y
                
                # 获取缩放后的旋转矩形的四个角点
                points = cv2.boxPoints(((orig_cx, orig_cy), (orig_w, orig_h), angle))
                final_regions.append(points.astype(np.float32))

        processing_time = time.time() - start_time
        metadata = {
            'processing_time': processing_time,
            'detection_mode': 'ppocr_v3', # <--- 使用一个固定的值或移除此键
            'total_regions': len(final_regions),
            'detection_method': 'PP-OCRv3'
        }
        
        logger.info(f"PP-OCRv3文本检测完成: {len(final_regions)}个区域, 耗时: {processing_time:.3f}秒")
        return final_regions, metadata

    def _decode_predictions(self, scores, geometry):
        """从模型输出解码边界框和置信度 (适配PP-OCR的EAST-like输出)"""
        rects = []
        confidences = []
        height, width = scores.shape
        
        for y in range(height):
            for x in range(width):
                score = scores[y, x]
                if score < self.threshold:
                    continue
                
                # 几何信息解码
                geo = geometry[:, y, x]
                d1, d2, d3, d4, angle = geo
                
                # 计算旋转矩形
                cos, sin = math.cos(angle), math.sin(angle)
                offset_x, offset_y = x * 4.0, y * 4.0
                
                box_height = d1 + d3
                box_width = d2 + d4
                
                # 计算中心点
                center_x = offset_x + cos * (d2 - d4) / 2 - sin * (d1 - d3) / 2
                center_y = offset_y + sin * (d2 - d4) / 2 + cos * (d1 - d3) / 2
                
                # PP-OCR的旋转角度定义是从水平轴逆时针，范围[-45, 45]，OpenCV需要度数
                angle_deg = angle * (180 / math.pi)
                
                rot_rect = ((center_x, center_y), (box_width, box_height), angle_deg)
                
                rects.append(rot_rect)
                confidences.append(float(score))
                
        return rects, confidences
class UnifiedObjectDetector:
    """
    一个统一的目标检测器，使用YOLOv4-tiny识别文本、表格和基础图形。
    版本: 2.0 - 实现了模型的自动下载、验证与加载。
    """
    def __init__(self, logger_func: Callable, cfg_path: str, weights_path: str, names_path: str):
        """
        UnifiedObjectDetector 的构造函数 (V3.32 - 用户可配置模型版)。
        - 使用用户提供的路径加载YOLOv4-tiny模型。
        - 不再执行自动下载，只检查文件是否存在。
        """
        self.log = logger_func
        self.net = None
        self.classes = []
        self.output_layers = []
        self.class_map = {
            "person": "text", "book": "text", "cell phone": "text",
            "laptop": "graphic", "tv": "graphic", "remote": "graphic",
            "dining table": "table"
        }

        # 1. 检查用户提供的文件是否存在
        for path, name in [(weights_path, "权重文件"), (cfg_path, "配置文件"), (names_path, "类别文件")]:
            if not os.path.exists(path):
                self.log(f"❌ YOLO {name} '{path}' 不存在，统一对象检测功能将不可用。", "ERROR")
                messagebox.showerror("YOLO模型文件缺失", f"YOLO {name}未找到：\n{path}\n\n请在“全元素检测引擎”设置中指定正确的文件路径。")
                return

        # 2. 尝试加载YOLO网络
        try:
            self.net = cv2.dnn.readNetFromDarknet(cfg_path, weights_path)
            self.net.setPreferableBackend(cv2.dnn.DNN_BACKEND_OPENCV)
            self.net.setPreferableTarget(cv2.dnn.DNN_TARGET_CPU)
            with open(names_path, "r", encoding='utf-8') as f:
                self.classes = [line.strip() for line in f.readlines()]

            layer_names = self.net.getLayerNames()
            unconnected_layers_indices = self.net.getUnconnectedOutLayers()
            if isinstance(unconnected_layers_indices, np.ndarray):
                unconnected_layers_indices = unconnected_layers_indices.flatten()
            self.output_layers = [layer_names[i - 1] for i in unconnected_layers_indices]
            
            self.log("✅ 用户指定的YOLOv4-tiny统一对象检测器加载成功。", "SUCCESS")

        except Exception as e:
            self.log(f"❌ 加载用户指定的YOLO模型失败: {e}", "ERROR")
            messagebox.showerror("YOLO模型加载失败", f"加载YOLO模型时出错：\n{e}\n\n请检查文件是否正确且未损坏。")
            self.net = None
    
    
    
    
    def detect_all_objects(self, image: np.ndarray) -> List[Dict]:
        """
        在图像中检测所有对象（文本、表格、图形）。
        这是一个混合方法，结合了YOLO的深度学习检测和经典CV的轮廓分析。
        Args:
            image (np.ndarray): 输入的BGR图像。
        Returns:
            List[Dict]: 包含所有检测到对象信息的列表。
        """
        if self.net is None:
            self.log("⚠️ YOLO网络未加载，跳过统一对象检测。", "WARNING")
            return []

        height, width, _ = image.shape
        
        # 1. 使用YOLO进行深度学习对象检测
        blob = cv2.dnn.blobFromImage(image, 1/255.0, (416, 416), swapRB=True, crop=False)
        self.net.setInput(blob)
        outs = self.net.forward(self.output_layers)

        boxes = []
        confidences = []
        class_ids = []

        for out in outs:
            for detection in out:
                scores = detection[5:]
                class_id = np.argmax(scores)
                confidence = scores[class_id]
                if confidence > 0.3:  # 置信度阈值
                    center_x = int(detection[0] * width)
                    center_y = int(detection[1] * height)
                    w = int(detection[2] * width)
                    h = int(detection[3] * height)
                    x = int(center_x - w / 2)
                    y = int(center_y - h / 2)
                    boxes.append([x, y, w, h])
                    confidences.append(float(confidence))
                    class_ids.append(class_id)
        
        # 应用非极大值抑制（NMS）以消除重叠的边界框
        indexes = cv2.dnn.NMSBoxes(boxes, confidences, 0.3, 0.4)
        
        detected_objects = []
        if len(indexes) > 0:
            for i in indexes.flatten():
                x, y, w, h = boxes[i]
                label = self.classes[class_ids[i]]
                
                # 使用类别映射转换标签
                mapped_label = self.class_map.get(label, "unknown")
                
                # 只添加被映射为有效类别的对象
                if mapped_label != "unknown":
                    detected_objects.append({
                        "bbox": [x, y, x + w, y + h],
                        "label": mapped_label,
                        "confidence": confidences[i]
                    })

        # 2. 使用经典计算机视觉方法补充基础图形检测
        gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
        canny_edges = cv2.Canny(gray, 50, 150)
        contours, _ = cv2.findContours(canny_edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)

        for contour in contours:
            area = cv2.contourArea(contour)
            if area < 200 or area > width * height * 0.8:
                continue

            peri = cv2.arcLength(contour, True)
            approx = cv2.approxPolyDP(contour, 0.03 * peri, True)
            x, y, w, h = cv2.boundingRect(approx)
            shape_label = "unknown"

            if len(approx) == 4:
                roi = gray[y:y+h, x:x+w]
                # 棋盘格/图案的特征：内部有大量角点
                corners = cv2.goodFeaturesToTrack(roi, 30, 0.01, 10)
                if corners is not None and len(corners) > 20:
                    shape_label = "pattern"
                else:
                    shape_label = "rectangle"
            elif len(approx) > 7: # 近似为圆
                (cx, cy), radius = cv2.minEnclosingCircle(contour)
                circle_area = np.pi * (radius ** 2)
                if circle_area > 0 and 0.8 < area / circle_area < 1.2:
                    shape_label = "ellipse"

            # 线条的特征：宽高比极端
            if w > h * 8 or h > w * 8:
                shape_label = "line"
            
            if shape_label != "unknown":
                detected_objects.append({
                    "bbox": [x, y, x + w, y + h],
                    "label": shape_label,
                    "confidence": 0.95  # 几何方法确定性高，给一个较高的置信度
                })

        return detected_objects
class OCRLanguage(Enum):
    """OCR语言枚举"""
    AUTO = "auto"          # 自动检测
    CHINESE = "chi_sim"    # 简体中文
    ENGLISH = "eng"        # 英文
    CHINESE_TRAD = "chi_tra"  # 繁体中文
    JAPANESE = "jpn"       # 日文
    KOREAN = "kor"         # 韩文
    MULTI = "chi_sim+eng"  # 中英混合


class TextQualityLevel(Enum):
    """文本图像质量等级枚举"""
    EXCELLENT = "excellent" # 优秀
    GOOD = "good"           # 良好
    FAIR = "fair"           # 一般
    POOR = "poor"           # 差

class CVOCRException(Exception):
    """CVOCR自定义异常"""
    def __init__(self, message: str, error_code: str = None, details: dict = None):
        super().__init__(message)
        self.error_code = error_code
        self.details = details or {}






class ImageQualityLevel(Enum):
    """图像质量等级枚举"""
    EXCELLENT = "excellent"
    GOOD = "good"
    FAIR = "fair"
    POOR = "poor"
class TextOrientation(Enum):
    """文本方向枚举"""
    HORIZONTAL = "horizontal"
    VERTICAL = "vertical"
    MIXED = "mixed"


class CVOCRVersionManager:
    """CVOCR版本管理器 - 处理不同版本的兼容性"""
    
    @staticmethod
    def get_system_info() -> Dict[str, str]:
        """获取系统信息"""
        return {
            'python_version': sys.version.split()[0],
            'platform': platform.system(),
            'platform_version': platform.version(),
            'architecture': platform.architecture()[0],
            'processor': platform.processor(),
            'hostname': platform.node()
        }
    
    @staticmethod
    def get_tesseract_version(tesseract_path: Optional[str] = None) -> str:
        """获取Tesseract版本"""
        try:
            import pytesseract
            # 尝试使用传入的路径，否则使用 pytesseract.pytesseract.tesseract_cmd
            # 如果都没有，则回退到系统PATH中的tesseract
            original_cmd = None
            if tesseract_path and os.path.exists(tesseract_path):
                original_cmd = pytesseract.pytesseract.tesseract_cmd
                pytesseract.pytesseract.tesseract_cmd = tesseract_path
            
            version = pytesseract.get_tesseract_version()
            
            
            if original_cmd is not None: 
                pytesseract.pytesseract.tesseract_cmd = original_cmd # 恢复原路径
            return str(version)
        except ImportError:
            return "unknown (pytesseract not installed)"
        except Exception as e:
            logger.warning(f"获取Tesseract版本失败: {e}")
            return "unknown (Error)"
    
    @staticmethod
    def get_transformers_version() -> str:
        """获取Transformers版本"""
        try:
            import transformers
            return transformers.__version__
        except ImportError:
            return "unknown (transformers not installed)"
        except Exception as e:
            logger.warning(f"获取Transformers版本失败: {e}")
            return "unknown (Error)"
    
    @staticmethod
    def get_opencv_version() -> str:
        """获取OpenCV版本"""
        try:
            import cv2
            return cv2.__version__
        except ImportError:
            return "unknown (opencv not installed)"
        except Exception as e:
            logger.warning(f"获取OpenCV版本失败: {e}")
            return "unknown (Error)"
    
    @staticmethod
    def get_torch_version() -> str:
        """获取PyTorch版本"""
        try:
            import torch
            return torch.__version__
        except ImportError:
            return "unknown (torch not installed)"
        except Exception as e:
            logger.warning(f"获取PyTorch版本失败: {e}")
            return "unknown (Error)"
    
    @staticmethod
    def check_compatibility(tesseract_path: Optional[str] = None) -> Tuple[bool, List[str]]:
        """检查版本兼容性"""
        issues = []
        
        # 检查Python版本
        python_version = tuple(map(int, sys.version.split()[0].split('.')[:2]))
        if python_version < (3, 8):
            issues.append(f"Python版本过低: {sys.version.split()[0]}，建议升级到3.8+")
        
        # 检查PyTorch
        try:
            import torch
            torch_version = torch.__version__
            if tuple(map(int, torch_version.split('.')[:2])) < (1, 12):
                issues.append(f"PyTorch版本过低: {torch_version}，建议升级到1.12+")
        except ImportError:
            issues.append("PyTorch未安装 - 高级功能需要PyTorch支持")
        except Exception as e:
            issues.append(f"检查PyTorch版本异常: {e}")
        
        # 检查Tesseract
        try:
            import pytesseract
            # 尝试获取版本，会触发 Tesseract 可执行文件的检查
            CVOCRVersionManager.get_tesseract_version(tesseract_path)
        except ImportError:
            issues.append("pytesseract未安装 - 基础OCR功能不可用")
        except Exception as e:
            issues.append(f"Tesseract不可用: {e}")
        
        # 检查OpenCV
        try:
            import cv2
            cv_version = cv2.__version__
            if tuple(map(int, cv_version.split('.')[:2])) < (4, 5):
                issues.append(f"OpenCV版本过低: {cv_version}，建议升级到4.5+")
        except ImportError:
            issues.append("OpenCV未安装 - 图像处理功能不可用")
        except Exception as e:
            issues.append(f"检查OpenCV版本异常: {e}")
        
        # 检查transformers
        try:
            import transformers
            trans_version = transformers.__version__
            if tuple(map(int, trans_version.split('.')[:2])) < (4, 25):
                issues.append(f"Transformers版本过低: {trans_version}，建议升级到4.25+")
        except ImportError:
            issues.append("Transformers未安装 - AI增强功能不可用")
        except Exception as e:
            issues.append(f"检查Transformers版本异常: {e}")
        
        # 检查PIL/Pillow
        try:
            from PIL import Image
            import PIL
            pil_version = PIL.__version__
            if tuple(map(int, pil_version.split('.')[:2])) < (9, 0):
                issues.append(f"Pillow版本过低: {pil_version}，建议升级到9.0+")
        except ImportError:
            issues.append("Pillow未安装 - 图像处理功能不可用")
        
        # 检查NumPy
        try:
            import numpy
            np_version = numpy.__version__
            if tuple(map(int, np_version.split('.')[:2])) < (1, 21):
                issues.append(f"NumPy版本过低: {np_version}，建议升级到1.21+")
        except ImportError:
            issues.append("NumPy未安装")
        
        return len(issues) == 0, issues
    
    @staticmethod
    def get_dependency_versions(tesseract_path: Optional[str] = None) -> Dict[str, str]:
        """获取所有依赖版本信息"""
        versions = {
            'cvocr_gui': CVOCRConstants.VERSION,
            'python': sys.version.split()[0],
            'tesseract': CVOCRVersionManager.get_tesseract_version(tesseract_path),
            'transformers': CVOCRVersionManager.get_transformers_version(),
            'opencv': CVOCRVersionManager.get_opencv_version(),
            'torch': CVOCRVersionManager.get_torch_version()
        }
        
        # 获取其他库版本
        # --- 修正5: 添加 'psutil' 到版本检查列表 ---
        for lib_name in ['numpy', 'PIL', 'tkinter', 'psutil']:
            try:
                lib = __import__(lib_name)
                # tkinter and PIL might not have __version__ in the same way
                if lib_name == 'PIL':
                    # Pillow库的版本信息存储在PIL.__version__
                    from PIL import __version__ as pil_version
                    versions[lib_name] = pil_version
                elif lib_name == 'tkinter':
                    # tkinter的版本与其依赖的Tcl/Tk版本相关
                    import tkinter as tk
                    versions[lib_name] = tk.Tcl().eval('info patchlevel')
                else:
                    # 对于大多数库，可以直接获取__version__属性
                    versions[lib_name] = getattr(lib, '__version__', 'unknown')
            except ImportError:
                versions[lib_name] = 'not installed'
            except Exception:
                versions[lib_name] = 'unknown'
        
        return versions
        
        
class AdvancedTextImageProcessor:
    """高级文本图像处理器 - 为OCR识别优化"""
    
    def __init__(self):
        # 默认配置，这些值会被传入的 options 或 GUI 的设置覆盖
        self.config = {
            # 图像尺寸参数
            'target_input_size': 1024,
            'max_image_size': CVOCRConstants.MAX_IMAGE_SIZE,
            'optimal_ocr_size': 1024,
            'min_image_size': CVOCRConstants.MIN_IMAGE_SIZE,
            
            # 增强的对比度和锐化参数范围 (如果不用GUI slider，可直接设为固定值)
            'contrast_factor_range': (1.1, 2.0),
            'brightness_adjustment_range': (-0.15, 0.25),
            'sharpness_factor_range': (1.0, 2.5),
            'gamma_correction_range': (0.8, 1.4),
            
            # 高级降噪参数范围
            'bilateral_d_range': (5, 13),
            'bilateral_sigma_color_range': (25, 100),
            'bilateral_sigma_space_range': (25, 100),
            'gaussian_kernel_size_range': (3, 7),
            
            # OCR优化参数 (在GUI中通过settings传递，这里作为默认值)
            'enable_deskew': True,
            'deskew_angle_threshold': 0.5,
            'enable_deblur': True, # 模糊检测/修复，目前代码中未明确实现，可作为未来扩展点
            'enable_text_enhancement': True, # 文本增强，由形态学和锐化等实现
            'enable_morphology': True, # 形态学操作
            'enable_adaptive_threshold': True, # 自适应二值化
            'remove_borders': True, # 移除图像边框
            'border_threshold': 10, # 边框移除阈值
            'crop_to_content': True, # 裁剪到实际内容
            'page_border_detection': True, # 页面边框检测 (用于透视校正等)
            'shadow_removal': True, # 阴影移除
            'denoise_strength': 0.1, # 高级降噪强度 (对应fastNlMeansDenoising)
            'edge_preservation': 0.8, # 边缘保留强度 (与高级降噪配合)
            'unsharp_mask': True,     # 反锐化掩模
            'unsharp_radius': 1.0,    # 反锐化掩模半径
            'unsharp_amount': 1.0,    # 反锐化掩模强度
            'histogram_equalization': True, # 直方图均衡化
            'bilateral_filter': True, # 双边滤波
            'bilateral_d': 9, # 双边滤波直径
            'bilateral_sigma_color': 75.0, # 双边滤波颜色空间标准差
            'bilateral_sigma_space': 75.0, # 双边滤波空间标准差
            'apply_clahe': True, # CLAHE (对比度受限自适应直方图均衡)
            'clahe_clip_limit': 2.0, # CLAHE 裁剪限制
            'clahe_tile_grid_size': (8, 8), # CLAHE 网格大小
            'adaptive_block_size': 11, # 自适应阈值块大小
            'adaptive_c_constant': 2, # 自适应阈值 C 常量
        }
        
        # 处理结果缓存
        self._processing_cache = {}
        self._cache_max_size = 50 # 最大缓存条目数
        self._cache_expiry = {} # 缓存过期时间记录
        
        # 性能监控
        self._processing_stats = {
            'total_processed': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'average_processing_time': 0.0,
            'processing_times': deque(maxlen=100) # 记录最近100次处理时间
        }
        
        logger.info("高级文本图像处理器已初始化")

    @staticmethod
    def validate_image(image_path: str) -> Tuple[bool, str]:
        """
        增强版图像验证方法。
        检查文件是否存在、大小、格式、尺寸及数据完整性。
        """
        if not isinstance(image_path, (str, Path)):
            return False, "无效的文件路径类型"
        
        image_path = str(image_path)
        
        if not os.path.exists(image_path):
            return False, "文件不存在"
        
        try:
            file_size = os.path.getsize(image_path)
            if file_size == 0:
                return False, "文件为空"
            
            if file_size > CVOCRConstants.MAX_FILE_SIZE:
                return False, f"文件过大 (超过{CVOCRConstants.MAX_FILE_SIZE // (1024*1024)}MB)"
            
            file_ext = os.path.splitext(image_path)[1].lower()
            if file_ext not in CVOCRConstants.SUPPORTED_IMAGE_FORMATS:
                return False, f"不支持的文件格式: {file_ext}"
            
            with Image.open(image_path) as img:
                width, height = img.size
                
                if width == 0 or height == 0:
                    return False, "图像尺寸为零"
                
                if width < CVOCRConstants.MIN_IMAGE_SIZE or height < CVOCRConstants.MIN_IMAGE_SIZE:
                    return False, f"图像尺寸过小 (小于{CVOCRConstants.MIN_IMAGE_SIZE}x{CVOCRConstants.MIN_IMAGE_SIZE}像素)"
                
                if width > CVOCRConstants.MAX_IMAGE_SIZE or height > CVOCRConstants.MAX_IMAGE_SIZE:
                    return False, f"图像尺寸过大 (大于{CVOCRConstants.MAX_IMAGE_SIZE}x{CVOCRConstants.MAX_IMAGE_SIZE}像素)"
                
                if img.mode not in ['RGB', 'RGBA', 'L', 'P', '1', 'CMYK']:
                    return False, f"不支持的图像模式: {img.mode}"
                
                try:
                    img.load()
                    img_array = np.array(img)
                    
                    if img_array.std() < 1: # 检查图像内容多样性，防止全黑/全白或损坏图像
                        return False, "图像内容过于单调，可能损坏或无有效内容"
                    
                    if len(img_array.shape) > 3: # 不支持4D以上图像
                        return False, "不支持的图像维度"
                        
                except Exception as e:
                    return False, f"图像数据损坏: {str(e)}"
                
                return True, "图像有效"
                
        except Exception as e:
            return False, f"图像格式错误或损坏: {str(e)}"
    
    def intelligent_preprocess_image(self, image_path: str, **options) -> Tuple[Optional[np.ndarray], str, Dict]:
        """
        【最终重构版】智能图像预处理核心方法
        - 根据用户设置（全元素检测 vs 纯文本识别）选择合适的预处理策略。
        - 动态应用UI选项，确保用户设置在所有子流程中生效。
        - 为预览和日志提供清晰、详细的处理步骤信息。
        """
        start_time = time.time()
        
        try:
            # 1. 验证输入图像的有效性
            is_valid, validation_msg = self.validate_image(image_path)
            if not is_valid:
                logger.error(f"图像验证失败: {validation_msg}")
                return None, f"图像验证失败: {validation_msg}", {}

            # 2. 关键步骤：将传入的options动态更新到实例配置中
            self.config.update(options)
            logger.debug(f"DEBUG: Preprocessing config updated with options from UI: {options}")
            
            # 3. 生成缓存键并检查缓存
            cache_key = self._generate_cache_key(image_path, options)
            cached_result = self._get_from_cache(cache_key)
            if cached_result is not None:
                self._processing_stats['cache_hits'] += 1
                logger.info("使用缓存的图像预处理结果。")
                return cached_result['image'], cached_result['message'], cached_result['metadata']
            
            self._processing_stats['cache_misses'] += 1
            
            # 4. 读取图像
            image = cv2.imread(image_path)
            if image is None:
                try:
                    pil_img = Image.open(image_path).convert('RGB')
                    image = cv2.cvtColor(np.array(pil_img), cv2.COLOR_RGB2BGR)
                except Exception as e:
                    raise CVOCRException(f"无法读取图像文件: {str(e)}", "IMAGE_READ_ERROR")
            
            original_shape = image.shape
            logger.info(f"开始智能OCR预处理图像: {image_path}, 原始尺寸: {original_shape}")
            
            # 5. 根据更新后的 self.config 决定预处理策略
            enable_preprocessing = self.config.get('enable_preprocessing', False)
            use_advanced_segmentation = self.config.get('enable_advanced_segmentation', False)
            
            processed_image = image.copy()
            process_operations = []
            quality_level = TextQualityLevel.FAIR
            quality_metrics = {}

            if enable_preprocessing:
                if use_advanced_segmentation:
                    logger.info("工作流: 为全元素检测准备图像（简化预处理）")
                    process_operations.append("[模式: 全元素检测准备]")
                    processed_image = self._optimize_image_size(processed_image)
                    process_operations.append("尺寸与通道标准化")
                    if len(processed_image.shape) == 2:
                        processed_image = cv2.cvtColor(processed_image, cv2.COLOR_GRAY2BGR)
                    elif processed_image.shape[2] == 4:
                        processed_image = cv2.cvtColor(processed_image, cv2.COLOR_BGRA2BGR)
                    if self.config.get('enable_deskew', False):
                        gray_for_deskew = cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                        deskewed_gray, angle = self._deskew_image(gray_for_deskew, self.config.get('deskew_angle_threshold', 0.5))
                        if angle != 0.0:
                            center = (image.shape[1] // 2, image.shape[0] // 2)
                            rotation_matrix = cv2.getRotationMatrix2D(center, angle, 1.0)
                            processed_image = cv2.warpAffine(processed_image, rotation_matrix,
                                                       (image.shape[1], image.shape[0]),
                                                       flags=cv2.INTER_CUBIC, borderMode=cv2.BORDER_REPLICATE)
                            process_operations.append(f"倾斜校正({angle:.2f}°)")
                    process_operations.append("(注: 此模式下跳过复杂增强以保证检测精度)")
                else:
                    logger.info("工作流: 为整页纯文本识别进行全面预处理")
                    process_operations.append("[模式: 整页纯文本识别]")
                    processed_image, adaptive_ops = self.adaptive_text_preprocessing(image, **self.config)
                    process_operations.extend(adaptive_ops)
            else:
                logger.info("工作流: 智能预处理已禁用")
                process_operations.append("[模式: 预处理已禁用]")
                processed_image = self._optimize_image_size(image)
                process_operations.append("基础尺寸优化")
                if len(processed_image.shape) == 2:
                    processed_image = cv2.cvtColor(processed_image, cv2.COLOR_GRAY2BGR)
                    process_operations.append("灰度转BGR")

            # 6. 记录处理时间和元数据
            processing_time = time.time() - start_time
            self._update_processing_stats(processing_time)
            
            
            

            metadata = {
                
                'quality_level': quality_level.value if enable_preprocessing and not use_advanced_segmentation else 'N/A',
                'quality_score': quality_metrics.get('quality_score', 0) if enable_preprocessing and not use_advanced_segmentation else 'N/A',
                'quality_metrics': quality_metrics if enable_preprocessing and not use_advanced_segmentation else {},
                'operations': process_operations,
                'processing_time': processing_time,
                'original_shape': original_shape,
                'final_shape': processed_image.shape,
                'settings': options,
                'timestamp': datetime.now().isoformat()
            }
            
            # 7. 将处理结果添加到缓存
            cache_data = {
                'image': processed_image.copy(),
                'message': "智能OCR预处理成功" if enable_preprocessing else "基础处理成功",
                'metadata': metadata
            }
            self._add_to_cache(cache_key, cache_data)
            
            success_msg = f"{'智能OCR预处理成功' if enable_preprocessing else '基础处理成功'} (耗时: {processing_time:.2f}s)"
            logger.info(f"{success_msg}, 应用操作: {', '.join(metadata['operations'])}")
            
            self._processing_stats['total_processed'] += 1
            
            return processed_image, success_msg, metadata
            
        except CVOCRException as e:
            raise e
        except Exception as e:
            error_msg = f"智能OCR预处理失败: {str(e)}"
            logger.error(f"{error_msg}\n{traceback.format_exc()}")
            return None, error_msg, {'error': str(e), 'traceback': traceback.format_exc()}
    
    
    
    
    def assess_text_image_quality(self, image: np.ndarray) -> Tuple[TextQualityLevel, Dict]:
        """
        文本图像质量评估方法。
        评估图像的对比度、清晰度、亮度、噪声和文本特征，返回一个质量等级和详细指标。
        """
        try:
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image.copy()
            
            metrics = {}
            
            # 对比度评估 (标准差和均值)
            contrast_std = np.std(gray)
            contrast_mean = np.mean(gray)
            metrics['contrast_std'] = float(contrast_std)
            metrics['contrast_mean'] = float(contrast_mean)
            
            # 清晰度评估 (拉普拉斯算子方差和Sobel边缘强度)
            laplacian_var = cv2.Laplacian(gray, cv2.CV_64F).var()
            sobel_x = cv2.Sobel(gray, cv2.CV_64F, 1, 0, ksize=3)
            sobel_y = cv2.Sobel(gray, cv2.CV_64F, 0, 1, ksize=3)
            sobel_combined = np.sqrt(sobel_x**2 + sobel_y**2)
            sobel_mean = np.mean(sobel_combined)
            
            metrics['sharpness_laplacian'] = float(laplacian_var)
            metrics['sharpness_sobel'] = float(sobel_mean)
            
            # 亮度分布评估 (均值、标准差和熵)
            brightness_mean = np.mean(gray)
            brightness_std = np.std(gray)
            brightness_hist = cv2.calcHist([gray], [0], None, [256], [0, 256])
            brightness_entropy = -np.sum((brightness_hist / np.sum(brightness_hist)) * 
                                        np.log2((brightness_hist / np.sum(brightness_hist)) + 1e-10))
            
            metrics['brightness_mean'] = float(brightness_mean)
            metrics['brightness_std'] = float(brightness_std)
            metrics['brightness_entropy'] = float(brightness_entropy)
            
            # 噪声评估
            noise_level = self._estimate_noise(gray)
            metrics['noise_level'] = float(noise_level)
            
            # 文本特征检测
            text_features_score = self._assess_text_features(gray)
            metrics['text_features_score'] = float(text_features_score)
            
            # 结构特征评估
            structure_score = self._assess_structure_features(gray)
            metrics['structure_score'] = float(structure_score)
            
            # 综合质量评分
            quality_score = self._calculate_text_quality_score(metrics)
            metrics['quality_score'] = float(quality_score)
            
            # 根据综合评分确定质量等级
            if quality_score >= 85:
                level = TextQualityLevel.EXCELLENT
            elif quality_score >= 70:
                level = TextQualityLevel.GOOD
            elif quality_score >= 50:
                level = TextQualityLevel.FAIR
            else:
                level = TextQualityLevel.POOR
            
            return level, metrics
            
        except Exception as e:
            logger.error(f"文本图像质量评估失败: {e}")
            return TextQualityLevel.FAIR, {'error': str(e)}
    
    def _assess_text_features(self, gray: np.ndarray) -> float:
        """评估文本特征，例如边缘密度、线条密度和文本区域数量。"""
        try:
            # 边缘检测 (Canny)
            edges = cv2.Canny(gray, 50, 150)
            edge_density = np.sum(edges > 0) / (gray.shape[0] * gray.shape[1])
            
            # 水平和垂直线检测 (形态学开运算)
            kernel_h = cv2.getStructuringElement(cv2.MORPH_RECT, (25, 1))
            kernel_v = cv2.getStructuringElement(cv2.MORPH_RECT, (1, 25))
            
            horizontal_lines = cv2.morphologyEx(edges, cv2.MORPH_OPEN, kernel_h)
            vertical_lines = cv2.morphologyEx(edges, cv2.MORPH_OPEN, kernel_v)
            
            h_line_density = np.sum(horizontal_lines > 0) / (gray.shape[0] * gray.shape[1])
            v_line_density = np.sum(vertical_lines > 0) / (gray.shape[0] * gray.shape[1])
            
            # 文本区域检测 (MSER，需要安装opencv-contrib-python)
            try:
                mser = cv2.MSER_create()
                regions, _ = mser.detectRegions(gray)
                text_region_score = min(len(regions) / 100, 1.0)  # 归一化得分
            except Exception:
                logger.warning("MSER文本区域检测失败，可能缺少opencv-contrib-python。使用默认分数。")
                text_region_score = 0.5 # 失败时使用一个中等分数
            
            # 文本特征综合评分
            text_score = (
                edge_density * 100 + 
                h_line_density * 200 + 
                v_line_density * 100 +
                text_region_score * 50
            )
            return min(text_score, 100)
            
        except Exception as e:
            logger.error(f"文本特征评估失败: {e}")
            return 50.0
    
    def _assess_structure_features(self, gray: np.ndarray) -> float:
        """评估图像的结构特征，例如梯度幅度和局部二值模式 (LBP) 特征。"""
        try:
            # 计算图像的梯度 (Sobel)
            grad_x = cv2.Sobel(gray, cv2.CV_64F, 1, 0, ksize=3)
            grad_y = cv2.Sobel(gray, cv2.CV_64F, 0, 1, ksize=3)
            
            # 梯度幅值均值
            grad_mag = np.sqrt(grad_x**2 + grad_y**2)
            structure_score = np.mean(grad_mag) / 255 * 100
            
            # LBP特征 (需要scikit-image库)
            try:
                from skimage import feature
                lbp = feature.local_binary_pattern(gray, 8, 1, method='uniform')
                lbp_hist = np.histogram(lbp, bins=10)[0]
                lbp_uniformity = np.std(lbp_hist)
                structure_score += lbp_uniformity / 100 # 将均匀性加入结构得分
            except ImportError:
                logger.warning("scikit-image未安装，无法进行LBP特征评估。")
                pass # 如果没有scikit-image，则跳过LBP
            
            return min(structure_score, 100)
            
        except Exception as e:
            logger.error(f"结构特征评估失败: {e}")
            return 50.0
    
    def _estimate_noise(self, gray: np.ndarray) -> float:
        """噪声估计方法，使用高通滤波器和简化的Wiener滤波原理。"""
        try:
            # 使用高通滤波器估计噪声 (拉普拉斯算子)
            kernel = np.array([[-1, -1, -1], [-1, 8, -1], [-1, -1, -1]])
            convolved = cv2.filter2D(gray, cv2.CV_64F, kernel)
            noise = np.var(convolved) / 1000 # 经验性缩放
            
            # 使用Wiener滤波原理估计噪声 (图像减去高斯模糊后的差异)
            try:
                blurred = cv2.GaussianBlur(gray, (5, 5), 0)
                noise_alt = np.mean((gray.astype(float) - blurred.astype(float))**2)
                noise = (noise + noise_alt / 1000) / 2 # 结合两种估计
            except Exception:
                pass # 失败时保持原样
            
            return min(noise, 100)
            
        except Exception as e:
            logger.error(f"噪声估计失败: {e}")
            return 50.0
    
    def _calculate_text_quality_score(self, metrics: Dict) -> float:
        """根据各项评估指标，计算最终的综合文本质量评分。"""
        try:
            # 对比度评分 (归一化到0-100)
            contrast_score = min(max(metrics.get('contrast_std', 0) / 80 * 100, 0), 100)
            
            # 清晰度评分 (结合拉普拉斯和Sobel)
            sharpness_score = min(metrics.get('sharpness_laplacian', 0) / 1000 * 100, 100)
            sobel_score = min(metrics.get('sharpness_sobel', 0) / 50 * 100, 100)
            combined_sharpness = (sharpness_score + sobel_score) / 2
            
            # 噪声评分 (100 - 噪声级别)
            noise_score = max(100 - metrics.get('noise_level', 0), 0)
            
            # 文本特征评分 (直接使用评估结果)
            text_features_score = metrics.get('text_features_score', 0)
            
            # 亮度评分 (中心值128最佳，偏离越大分数越低)
            brightness = metrics.get('brightness_mean', 128)
            brightness_score = 100 - abs(brightness - 128) / 128 * 100
            brightness_score = max(brightness_score, 0)
            
            # 结构特征评分
            structure_score = metrics.get('structure_score', 50)
            
            # 亮度分布熵评分 (熵越高，分布越均匀，越好)
            brightness_entropy = metrics.get('brightness_entropy', 5)
            entropy_score = min(brightness_entropy / 8 * 100, 100) # 经验性归一化
            
            # 权重分配，计算总分
            total_score = (
                contrast_score * 0.20 +
                combined_sharpness * 0.25 +
                noise_score * 0.15 +
                brightness_score * 0.15 +
                text_features_score * 0.15 +
                structure_score * 0.05 +
                entropy_score * 0.05
            )
            
            return max(min(total_score, 100), 0) # 确保分数在0-100之间
            
        except Exception as e:
            logger.error(f"质量评分计算失败: {e}")
            return 50.0 # 失败时返回中等分数
    
    def adaptive_text_preprocessing(self, image: np.ndarray, quality_level: TextQualityLevel = None, **options) -> Tuple[np.ndarray, List[str]]:
        """
        【V4.1 - 完全手动控制最终版】
        预处理流程严格由用户通过 `options` 字典传递的开关决定。
        废除所有基于图像质量的自动判断策略，实现完全的用户控制。
        """
        try:
            operations = []
            # 从原始图像开始，根据后续步骤决定是否转换颜色空间
            processed_image = image.copy()
            
            # --- 核心流程：严格按照用户开关顺序执行 ---

            # 步骤 1: 转换为灰度图 (如果启用)
            # 这是后续很多操作的基础
            is_gray = False
            if options.get('enable_grayscale', False):
                if len(processed_image.shape) == 3:
                    processed_image = cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                    operations.append("转换为灰度图")
                is_gray = True
            
            # 步骤 2: 几何校正
            if options.get('enable_deskew', False):
                # 确保有灰度图用于倾斜检测
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                deskewed_image, angle = self._deskew_image(gray_for_op, options.get('deskew_angle_threshold', 0.5))
                if angle != 0.0:
                    # 将旋转应用到当前正在处理的图像上（可能是彩色或灰度）
                    center = (processed_image.shape[1] // 2, processed_image.shape[0] // 2)
                    M = cv2.getRotationMatrix2D(center, angle, 1.0)
                    processed_image = cv2.warpAffine(processed_image, M, (processed_image.shape[1], processed_image.shape[0]), 
                                                     flags=cv2.INTER_CUBIC, borderMode=cv2.BORDER_REPLICATE)
                    operations.append(f"几何: 倾斜校正({angle:.2f}°)")
            
            if options.get('page_border_detection', False):
                 # 页面检测最好在接近原始的图像上做
                 img_for_detect = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY) if len(image.shape) == 3 else image
                 processed_after_perspective = self._detect_and_crop_page(img_for_detect)
                 if processed_after_perspective.shape != img_for_detect.shape:
                     processed_image = processed_after_perspective
                     # 如果经过此步骤，图像肯定是灰度图了
                     is_gray = True
                     operations.append("几何: 页面检测与校正")

            # 步骤 3: 图像增强与清理 (这些操作通常在灰度图上效果更好)
            if options.get('shadow_removal', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                processed_image = self._remove_shadows(gray_for_op)
                is_gray = True
                operations.append("增强: 阴影移除")
            
            if options.get('bilateral_filter', False):
                # 双边滤波可以作用于彩色或灰度图
                processed_image = cv2.bilateralFilter(processed_image, 
                                                   d=options.get('bilateral_d', 9),
                                                   sigmaColor=int(options.get('bilateral_sigma_color', 75.0)),
                                                   sigmaSpace=int(options.get('bilateral_sigma_space', 75.0)))
                operations.append("降噪: 双边滤波")
            
            if options.get('histogram_equalization', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                processed_image = cv2.equalizeHist(gray_for_op)
                is_gray = True
                operations.append("增强: 直方图均衡化")
            
            if options.get('apply_clahe', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                clahe = cv2.createCLAHE(clipLimit=options.get('clahe_clip_limit', 2.0), 
                                      tileGridSize=options.get('clahe_tile_grid_size', (8, 8)))
                processed_image = clahe.apply(gray_for_op)
                is_gray = True
                operations.append("增强: CLAHE")

            if options.get('unsharp_mask', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                processed_image = self._unsharp_mask(gray_for_op, 
                                              radius=options.get('unsharp_radius', 1.0), 
                                              amount=options.get('unsharp_amount', 1.0))
                is_gray = True
                operations.append("增强: 反锐化掩模")

            # 步骤 4: 二值化 (如果启用)
            if options.get('enable_binarization', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                block_size = options.get('adaptive_block_size', 11); C_val = options.get('adaptive_c_constant', 2)
                if block_size % 2 == 0: block_size += 1
                processed_image = cv2.adaptiveThreshold(gray_for_op, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                                        cv2.THRESH_BINARY_INV, block_size, C_val)
                is_gray = True # 二值化后肯定是单通道图
                operations.append("转换: 自适应二值化")

            # 步骤 5: 最终裁剪操作 (通常在二值化后效果更好)
            if options.get('remove_borders', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                processed_image = self._remove_borders(gray_for_op, options.get('border_threshold', 10))
                is_gray = True
                operations.append("几何: 移除边框")

            if options.get('crop_to_content', False):
                gray_for_op = processed_image if is_gray else cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                processed_image, _ = self._crop_to_content(gray_for_op)
                is_gray = True
                operations.append("几何: 裁剪到内容")

            # --- 最终输出准备 ---
            # OCR引擎通常需要3通道BGR图像，这是为了最好的兼容性
            if is_gray:
                final_image = cv2.cvtColor(processed_image, cv2.COLOR_GRAY2BGR)
                operations.append("输出: 转换为BGR")
            else:
                final_image = processed_image

            if not operations:
                operations.append("无任何预处理操作")

            return final_image, operations
            
        except Exception as e:
            logger.error(f"手动控制预处理失败: {e}\n{traceback.format_exc()}")
            # 发生异常时，安全地返回原始图像的BGR版本
            if len(image.shape) == 2:
                return cv2.cvtColor(image, cv2.COLOR_BGR2BGR), ['错误: 预处理异常']
            return image, ['错误: 预处理异常']
    def _optimize_image_size(self, image: np.ndarray) -> np.ndarray:
        """
        基础尺寸优化，确保图像在OCR友好的尺寸范围内（1000-1600像素的最长边）。
        过大则缩小，过小则放大。
        """
        try:
            h, w = image.shape[:2]
            
            # 目标OCR友好的最长边范围
            target_ocr_long_side_min = 1000
            target_ocr_long_side_max = 1600
            
            long_side = max(h, w)
            
            # 如果图像过大，缩小到最大目标尺寸
            if long_side > target_ocr_long_side_max:
                scale = target_ocr_long_side_max / long_side
                new_w, new_h = int(w * scale), int(h * scale)
                image = cv2.resize(image, (new_w, new_h), interpolation=cv2.INTER_LANCZOS4) # 高质量缩小
                logger.debug(f"图像尺寸过大调整: {w}x{h} -> {new_w}x{new_h}")
                h, w = new_h, new_w # 更新尺寸
                long_side = max(h, w)

            # 如果图像过小，放大到最小目标尺寸
            if long_side < target_ocr_long_side_min:
                scale = target_ocr_long_side_min / long_side
                new_w, new_h = int(w * scale), int(h * scale)
                image = cv2.resize(image, (new_w, new_h), interpolation=cv2.INTER_CUBIC) # 双三次插值放大
                logger.debug(f"图像尺寸过小调整: {w}x{h} -> {new_w}x{new_h}")
                h, w = new_h, new_w # 更新尺寸
                long_side = max(h, w)
            
            # 强制转换为三通道 (如果不是)，OpenCV和Tesseract通常喜欢BGR格式
            if len(image.shape) == 2:
                image = cv2.cvtColor(image, cv2.COLOR_GRAY2BGR)
                logger.debug("图像转换为BGR三通道。")
                
            logger.debug(f"最终图像尺寸优化完成: {image.shape[1]}x{image.shape[0]}")
            return image
            
        except Exception as e:
            logger.error(f"图像尺寸优化失败: {e}\n{traceback.format_exc()}")
            return image
    
    # --- 图像处理辅助方法 (借鉴 ocr_toolkit.py) ---
    def _deskew_image(self, image: np.ndarray, angle_threshold: float = 0.5) -> Tuple[np.ndarray, float]:
        """
        倾斜校正，通过Canny边缘检测和Hough变换检测文本倾斜角度并进行旋转校正。
        """
        try:
            # 确保输入图像是灰度图
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image
            
            # 使用Canny边缘检测和Hough变换检测直线
            edges = cv2.Canny(gray, 50, 150, apertureSize=3)
            # 阈值100，minLineLength至少为图像宽度的1/4，maxLineGap为20像素
            lines = cv2.HoughLinesP(edges, 1, np.pi / 180, threshold=100,
                                   minLineLength=gray.shape[1] // 4, maxLineGap=20)
            
            if lines is not None and len(lines) > 0:
                angles = []
                for line in lines:
                    x1, y1, x2, y2 = line[0]
                    if x2 - x1 != 0:
                        angle = np.arctan2(y2 - y1, x2 - x1) * 180 / np.pi
                        if abs(angle) < 45: # 只关注接近水平的线
                            angles.append(angle)
                
                if angles:
                    median_angle = np.median(angles)
                    if abs(median_angle) > angle_threshold: # 只有角度超过阈值才进行旋转
                        center = (gray.shape[1] // 2, gray.shape[0] // 2)
                        rotation_matrix = cv2.getRotationMatrix2D(center, median_angle, 1.0)
                        rotated = cv2.warpAffine(gray, rotation_matrix,
                                               (gray.shape[1], gray.shape[0]),
                                               flags=cv2.INTER_CUBIC,
                                               borderMode=cv2.BORDER_REPLICATE) # 填充边缘
                        logger.debug(f"图像倾斜校正 {median_angle:.2f}度。")
                        return rotated, median_angle
            return image, 0.0 # 未检测到倾斜或倾斜角度过小
        except Exception as e:
            logger.warning(f"倾斜校正失败: {e}")
            return image, 0.0

    def _remove_shadows(self, image: np.ndarray) -> np.ndarray:
        """
        移除图像中的阴影，使用形态学操作和背景减法技术。
        """
        try:
            # 确保输入图像是灰度图
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image

            # 使用形态学操作获取图像背景（模拟阴影）
            kernel = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (20, 20)) # 椭圆核，尺寸可调
            background = cv2.morphologyEx(gray, cv2.MORPH_OPEN, kernel) # 开运算平滑图像，去除高频信息（文本），保留低频信息（背景/阴影）
            
            # 从原始图像减去背景，得到无阴影的图像
            diff = cv2.subtract(gray, background)
            
            # 对结果进行归一化处理，增强对比度
            norm_img = cv2.normalize(diff, None, 0, 255, cv2.NORM_MINMAX)
            
            # 使用除法来进一步减少阴影 (可选，可能会引入噪声)
            # 背景像素值为0时会导致除零，因此进行保护性处理
            background_float = background.astype(np.float32)
            image_float = gray.astype(np.float32)
            background_float = np.where(background_float == 0, 1, background_float) # 避免除零
            result = (image_float / background_float) * 255
            result = np.clip(result, 0, 255).astype(np.uint8) # 确保像素值在0-255范围内

            logger.debug("已移除图像阴影。")
            return result
        except Exception as e:
            logger.warning(f"阴影移除失败: {e}")
            return image

    def _process_borders(self, image: np.ndarray, remove_borders: bool, border_threshold: int, page_border_detection: bool) -> np.ndarray:
        """
        处理图像边框的通用接口。
        根据配置选择移除边框或进行页面边框检测及透视校正。
        """
        if page_border_detection:
            return self._detect_and_crop_page(image)
        elif remove_borders:
            return self._remove_borders(image, border_threshold)
        return image

    def _remove_borders(self, image: np.ndarray, threshold: int) -> np.ndarray:
        """
        移除图片中的均匀边框，通过检查边缘像素的平均强度。
        """
        try:
            h, w = image.shape[:2]
            
            # 检测上、下、左、右边框
            top, bottom, left, right = 0, h-1, 0, w-1
            
            # 检查前1/4高度
            for i in range(h // 4): 
                if np.mean(image[i, :]) > threshold:
                    top = i
                    break
            
            # 检查后1/4高度
            for i in range(h - 1, 3 * h // 4, -1): 
                if np.mean(image[i, :]) > threshold:
                    bottom = i
                    break
            
            # 检查前1/4宽度
            for i in range(w // 4): 
                if np.mean(image[:, i]) > threshold:
                    left = i
                    break
            
            # 检查后1/4宽度
            for i in range(w - 1, 3 * w // 4, -1): 
                if np.mean(image[:, i]) > threshold:
                    right = i
                    break
            
            # 裁剪图像，确保裁剪后有足够内容
            if top < bottom and left < right and (bottom - top > 50) and (right - left > 50): 
                logger.debug(f"移除边框: 从 {0},{0},{w},{h} 裁剪到 {left},{top},{right+1},{bottom+1}")
                return image[top:bottom+1, left:right+1]
            logger.debug("未检测到明显边框或裁剪区域过小，跳过边框移除。")
            return image
        except Exception as e:
            logger.warning(f"移除边框失败: {e}")
            return image

    def _detect_and_crop_page(self, image: np.ndarray) -> np.ndarray:
        """
        检测并裁剪到文档页面内容，支持透视校正。
        通过查找最大轮廓并近似为四边形来识别页面。
        """
        try:
            # 确保输入图像是灰度图
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image
            
            edges = cv2.Canny(gray, 50, 150) # 边缘检测
            contours, _ = cv2.findContours(edges, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE) # 查找外部轮廓
            
            if contours:
                largest_contour = max(contours, key=cv2.contourArea) # 找到最大轮廓
                epsilon = 0.02 * cv2.arcLength(largest_contour, True) # 近似多边形的精度
                approx = cv2.approxPolyDP(largest_contour, epsilon, True) # 近似多边形
                
                if len(approx) == 4: # 如果找到四个角点，则进行透视校正
                    points = approx.reshape(4, 2)
                    
                    # 排序角点：左上、右上、右下、左下
                    rect = np.zeros((4, 2), dtype=np.float32)
                    s = points.sum(axis=1)
                    rect[0] = points[np.argmin(s)]  # 左上 (x+y最小)
                    rect[2] = points[np.argmax(s)]  # 右下 (x+y最大)
                    
                    diff = np.diff(points, axis=1)
                    rect[1] = points[np.argmin(diff)]  # 右上 (y-x最小)
                    rect[3] = points[np.argmax(diff)]  # 左下 (y-x最大)
                    
                    # 计算新图像的尺寸 (基于矫正后的宽度和高度)
                    width_a = np.linalg.norm(rect[2] - rect[3])
                    width_b = np.linalg.norm(rect[1] - rect[0])
                    max_width = int(max(width_a, width_b))
                    
                    height_a = np.linalg.norm(rect[1] - rect[2])
                    height_b = np.linalg.norm(rect[0] - rect[3])
                    max_height = int(max(height_a, height_b))
                    
                    # 目标透视变换后的四个角点
                    dst = np.array([
                        [0, 0],
                        [max_width - 1, 0],
                        [max_width - 1, max_height - 1],
                        [0, max_height - 1]
                    ], dtype=np.float32)
                    
                    matrix = cv2.getPerspectiveTransform(rect, dst) # 计算透视变换矩阵
                    warped = cv2.warpPerspective(image, matrix, (max_width, max_height)) # 应用透视变换
                    logger.debug("已执行页面透视校正和裁剪。")
                    return warped
                else: # 未找到四个角点，使用最小外接矩形进行裁剪
                    x, y, w, h = cv2.boundingRect(largest_contour)
                    if w > 50 and h > 50: # 确保裁剪区域有效
                        logger.debug(f"已裁剪到最大轮廓矩形区域: {x},{y},{w},{h}。")
                        return image[y:y+h, x:x+w]
            logger.debug("未检测到有效页面边框，跳过页面检测裁剪。")
            return image
        except Exception as e:
            logger.warning(f"页面检测和裁剪失败: {e}")
            return image

    def _crop_to_content(self, image: np.ndarray) -> Tuple[np.ndarray, bool]:
        """
        裁剪图像的实际内容区域，移除空白边缘。
        通过查找非白色（非255）像素来确定内容边界。
        """
        try:
            # 确保输入图像是灰度图，因为我们通常需要找到非白色像素
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image

            # 找到所有非零（非白色）像素的坐标
            coords = cv2.findNonZero(gray)
            if coords is None: # 全白图像，没有内容
                logger.debug("图像内容全白，跳过裁剪到内容。")
                return image, False
            x, y, w, h = cv2.boundingRect(coords) # 获取内容区域的最小外接矩形
            
            # 添加少量边距，防止裁剪过紧
            margin = 5
            x = max(0, x - margin)
            y = max(0, y - margin)
            w = min(image.shape[1] - x, w + 2 * margin)
            h = min(image.shape[0] - y, h + 2 * margin)

            if w > 10 and h > 10: # 确保裁剪区域足够大，防止裁剪成空图
                cropped = image[y:y+h, x:x+w]
                logger.debug(f"已裁剪到内容区域: {x},{y},{w},{h}。")
                return cropped, True
            logger.debug("内容区域过小，跳过裁剪到内容。")
            return image, False
        except Exception as e:
            logger.warning(f"裁剪到内容失败: {e}")
            return image, False

    def _advanced_denoising(self, image: np.ndarray, strength: float, edge_preservation: float) -> np.ndarray:
        """
        高级降噪方法，使用OpenCV的`fastNlMeansDenoising`（非局部均值降噪）。
        支持通过`edge_preservation`参数调整降噪时边缘的保留程度。
        """
        try:
            # 确保输入图像是灰度图
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image

            h_param = int(strength * 30)  # 强度参数，可以调整，影响去噪效果
            template_window_size = 7       # 模板窗口大小
            search_window_size = 21        # 搜索窗口大小
            
            denoised = cv2.fastNlMeansDenoising(gray, None, h_param, template_window_size, search_window_size)
            
            # 如果边缘保留因子小于1.0，则将原始图像与降噪图像加权融合，以保留更多边缘细节
            if edge_preservation < 1.0:
                denoised = cv2.addWeighted(gray, edge_preservation, 
                                         denoised, 1.0 - edge_preservation, 0)
            logger.debug(f"执行高级降噪 (强度: {strength}, 边缘保留: {edge_preservation})。")
            return denoised
        except Exception as e:
            logger.warning(f"高级降噪失败: {e}，回退到高斯模糊。")
            # 失败时回退到高斯模糊
            kernel_size = max(3, int(strength * 10))
            if kernel_size % 2 == 0:
                kernel_size += 1
            return cv2.GaussianBlur(image, (kernel_size, kernel_size), 0)

    def _unsharp_mask(self, image: np.ndarray, radius: float = 1.0, amount: float = 1.0) -> np.ndarray:
        """
        反锐化掩模 (Unsharp Masking) 算法，用于增强图像细节和边缘。
        通过从原始图像中减去其模糊版本来创建锐化效果。
        """
        try:
            # 确保输入图像是灰度图
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image

            # 先进行高斯模糊
            # sigmaX 参数设置为 radius，kernel size 设为 (0,0) 表示根据 sigmaX 自动计算
            blurred = cv2.GaussianBlur(gray, (0, 0), radius)
            # 计算掩模：原始图像 - 模糊图像
            unsharp_mask_result = cv2.addWeighted(gray, 1.0 + amount, blurred, -amount, 0)
            unsharp_mask_result = np.clip(unsharp_mask_result, 0, 255).astype(np.uint8) # 确保像素值范围
            logger.debug(f"执行反锐化掩模 (半径: {radius}, 强度: {amount})。")
            return unsharp_mask_result
        except Exception as e:
            logger.warning(f"反锐化掩模失败: {e}")
            return image

    # --- 缓存管理方法 ---
    def _generate_cache_key(self, image_path: str, options: Dict) -> str:
        """生成缓存键，基于文件路径、修改时间及处理选项的MD5哈希。"""
        try:
            mtime = os.path.getmtime(image_path)
            options_str = json.dumps(options, sort_keys=True) # 确保选项顺序一致
            key_data = f"{image_path}_{mtime}_{options_str}"
            return hashlib.md5(key_data.encode()).hexdigest()
        except Exception as e:
            logger.error(f"生成缓存键失败: {e}")
            return f"error_{time.time()}"
    
    def _get_from_cache(self, cache_key: str) -> Optional[Dict]:
        """从缓存中获取结果，并检查是否过期。"""
        try:
            if cache_key in self._processing_cache:
                # 检查缓存是否过期
                if cache_key in self._cache_expiry:
                    if datetime.now() > self._cache_expiry[cache_key]:
                        self._remove_from_cache(cache_key)
                        logger.debug(f"缓存条目 {cache_key} 已过期并移除。")
                        return None
                
                logger.debug(f"缓存命中: {cache_key}")
                return self._processing_cache[cache_key]
            return None
        except Exception as e:
            logger.error(f"从缓存获取失败: {e}")
            return None
    
    def _add_to_cache(self, cache_key: str, result: Dict):
        """添加处理结果到缓存。当缓存满时，移除最旧的条目。"""
        try:
            # 清理过期缓存
            self._cleanup_expired_cache()
            
            # 如果缓存已满，删除最旧的条目 (基于过期时间)
            if len(self._processing_cache) >= self._cache_max_size:
                oldest_key = min(self._cache_expiry.keys(), 
                               key=lambda k: self._cache_expiry.get(k, datetime.now())) # 如果没有过期时间，则假定为当前时间
                self._remove_from_cache(oldest_key)
                logger.debug(f"缓存已满，移除最旧条目: {oldest_key}")
            
            # 添加新的缓存条目
            self._processing_cache[cache_key] = result
            self._cache_expiry[cache_key] = datetime.now() + timedelta(hours=CVOCRConstants.CACHE_EXPIRE_HOURS)
            logger.debug(f"添加新缓存条目: {cache_key}，有效期至: {self._cache_expiry[cache_key].strftime('%Y-%m-%d %H:%M:%S')}")
            
        except Exception as e:
            logger.error(f"添加到缓存失败: {e}")
    
    def _remove_from_cache(self, cache_key: str):
        """从缓存中删除指定的条目。"""
        try:
            self._processing_cache.pop(cache_key, None)
            self._cache_expiry.pop(cache_key, None)
            logger.debug(f"已从缓存中删除条目: {cache_key}")
        except Exception as e:
            logger.error(f"从缓存删除失败: {e}")
    
    def _cleanup_expired_cache(self):
        """定期清理所有已过期的缓存条目。"""
        try:
            now = datetime.now()
            expired_keys = [k for k, v in self._cache_expiry.items() if now > v]
            for key in expired_keys:
                self._remove_from_cache(key)
            if expired_keys:
                logger.info(f"已清理 {len(expired_keys)} 个过期缓存条目。")
        except Exception as e:
            logger.error(f"清理过期缓存失败: {e}")
    
    def _update_processing_stats(self, processing_time: float):
        """更新处理统计信息，包括平均处理时间。"""
        try:
            self._processing_stats['processing_times'].append(processing_time)
            self._processing_stats['average_processing_time'] = np.mean(list(self._processing_stats['processing_times']))
            logger.debug(f"更新处理统计：本次耗时 {processing_time:.2f}s，平均耗时 {self._processing_stats['average_processing_time']:.2f}s。")
        except Exception as e:
            logger.error(f"更新处理统计失败: {e}")
    
    def get_processing_stats(self) -> Dict:
        """获取当前处理统计信息。"""
        stats = self._processing_stats.copy()
        stats.update({
            'cache_size': len(self._processing_cache),
            'max_cache_size': self._cache_max_size,
            'cache_hit_rate': (stats['cache_hits'] / max(stats['cache_hits'] + stats['cache_misses'], 1)) * 100,
            'config': self.config.copy() # 包含当前的处理器配置
        })
        return stats
    
    def clear_cache(self):
        """清空所有处理缓存。"""
        try:
            self._processing_cache.clear()
            self._cache_expiry.clear()
            # 重置缓存统计
            self._processing_stats['cache_hits'] = 0
            self._processing_stats['cache_misses'] = 0
            logger.info("文本图像处理缓存已清理。")
        except Exception as e:
            logger.error(f"清理缓存失败: {e}")
class EnhancedCVOCRManager:
    """
    增强版CVOCR引擎管理器 (V3.29 - 终极技术栈升级版)
    - 彻底移除已被淘汰的FSRCNN模块。
    - 集成DBNet++作为默认的SOTA文本检测器。
    - 聚焦于DBNet++ + LayoutLMv2 + TrOCR + GPT-Neo + Tesseract的现代技术栈。
    """

    def __init__(self, logger_func: Callable):
        """
        增强版CVOCR引擎管理器的构造函数 (V3.32 - 延迟初始化版)。
        - 初始化所有模型占位符、配置和状态变量。
        - 接受来自GUI的日志函数。
        - 将 UnifiedObjectDetector 的实例化推迟到 initialize 方法中，以便使用用户配置。
        
        Args:
            logger_func (Callable): 一个用于记录日志并显示在GUI上的函数。
        """
        # ======================================================================
        # 1. 模型和处理器占位符
        # ======================================================================
        self.layoutlm_processor = None
        self.layoutlm_model = None
        self.trocr_processor = None
        self.trocr_model = None
        self.gpt_neo_tokenizer = None
        self.gpt_neo_model = None
        self.fsrcnn_model = None # 保留占位符
        
        # ### 修正：将检测器初始化为 None，推迟实例化 ###
        self.text_detector = None
        self.unified_detector = None
        
        # ======================================================================
        # 2. Tesseract 相关设置
        # ======================================================================
        self.tesseract_config = None
        self.tesseract_path = None
        
        # ======================================================================
        # 3. 状态与配置
        # ======================================================================
        self.is_initialized = False
        self.device = "cpu"
        self.version_info = {}
        self.language = OCRLanguage.AUTO
        
        self.logger_func = logger_func

        # 内部默认配置字典，将被UI设置覆盖
        self.config = {
            'psm': 6, 'oem': 3,
            'confidence_threshold': CVOCRConstants.DEFAULT_CONFIDENCE_THRESHOLD,
            'lang': 'chi_sim+eng',
            'enable_layout_analysis': False,
            'enable_context_analysis': False,
            'enable_transformer_ocr': False,
            'dpi': CVOCRConstants.DEFAULT_DPI,
            'enable_preprocessing_optimization': True,
            'batch_size': 1,
            'use_gpu': False,
            'model_precision': 'fp32',
            'tesseract_process_timeout': 300,
            'force_intensive_preprocessing': False,
            'ppocr_model_name': 'text_detection_cn_ppocrv3_2023may.onnx',
            # 新增YOLO路径的默认值
            'yolo_weights_path': 'yolov4-tiny.weights',
            'yolo_cfg_path': 'yolov4-tiny.cfg',
            'yolo_names_path': 'coco.names'
        }
        
        # ======================================================================
        # 4. 性能监控
        # ======================================================================
        self.performance_stats = {
            'total_recognitions': 0,
            'successful_recognitions': 0,
            'failed_recognitions': 0,
            'average_recognition_time': 0.0,
            'recognition_times': deque(maxlen=100),
            'component_usage': defaultdict(int)
        }
        
        logger.info("增强版CVOCR引擎管理器已创建 (等待初始化...)")
    @staticmethod
    def _execute_tesseract_subprocess(image_pil: Image.Image, tesseract_cmd_path: Optional[str], config_str: str, timeout: int) -> Dict:
        """
        Tesseract子进程执行器 (V3.7 - 配置文件模式修正版)
        - 使用临时配置文件传递参数，解决中文识别参数失效问题。
        """
        import subprocess
        import io
        import platform
        from collections import defaultdict
        import tempfile
        import os

        logger.debug(f"DEBUG: _execute_tesseract_subprocess 开始执行。")
        logger.debug(f"DEBUG: 接收到 config_str: {config_str}")

        tesseract_executable = tesseract_cmd_path if (tesseract_cmd_path and os.path.exists(tesseract_cmd_path)) else "tesseract"
        logger.debug(f"DEBUG: 确认Tesseract可执行文件路径: {tesseract_executable}")
        
        if not shutil.which(tesseract_executable) and not os.path.exists(tesseract_executable):
            logger.error(f"ERROR: Tesseract可执行文件未找到或不可执行: '{tesseract_executable}'。请检查路径配置。", exc_info=True)
            return {"status": "error", "message": f"Tesseract 可执行文件未找到或不可执行: '{tesseract_executable}'。"}

        temp_image_path = None
        temp_output_base = None
        temp_config_path = None
        temp_output_txt = None
        temp_output_tsv = None

        try:
            with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as temp_image_file:
                temp_image_path = temp_image_file.name
                if image_pil.mode not in ['RGB', 'L']:
                    image_pil = image_pil.convert('RGB')
                image_pil.save(temp_image_path, format='PNG')
            logger.debug(f"DEBUG: 图像已成功保存到临时文件: {temp_image_path} 用于Tesseract输入。")

            temp_output_base = tempfile.NamedTemporaryFile(delete=False).name
            temp_output_txt = temp_output_base + '.txt'
            temp_output_tsv = temp_output_base + '.tsv'

            config_to_use = ""
            if isinstance(config_str, list) and len(config_str) > 0:
                config_to_use = config_str[0][0]
            elif isinstance(config_str, str):
                config_to_use = config_str
            
            # 【核心修正】: 将配置写入临时文件
            config_parts = config_to_use.split()
            
            # 分离出 --psm, --oem, -l 这些主参数
            command_args = []
            # 将 -c 参数的内容写入配置文件
            config_file_lines = []

            i = 0
            while i < len(config_parts):
                part = config_parts[i]
                if part in ['--psm', '--oem', '-l']:
                    command_args.append(part)
                    if i + 1 < len(config_parts):
                        command_args.append(config_parts[i+1])
                        i += 1
                elif part == '-c':
                    if i + 1 < len(config_parts):
                        # 将 key=value 写入配置文件, Tesseract配置文件格式是 "key value"
                        config_file_lines.append(config_parts[i+1].replace('=', ' ', 1))
                        i += 1
                i += 1
            
            # 构建基础命令
            command_base = [tesseract_executable, temp_image_path, temp_output_base] + command_args

            # 如果有需要写入配置文件的参数
            if config_file_lines:
                with tempfile.NamedTemporaryFile(mode='w+', delete=False, suffix='.cfg', encoding='utf-8') as temp_config_file:
                    temp_config_path = temp_config_file.name
                    temp_config_file.write('\n'.join(config_file_lines))
                # 将配置文件名作为最后一个参数添加到命令中
                command_base.append(os.path.basename(temp_config_path).split('.')[0])
                logger.debug(f"DEBUG: Tesseract 配置已写入临时文件: {temp_config_path}")
            
            command_txt = command_base
            command_tsv = command_base + ['tsv']
            
            logger.debug(f"DEBUG: 最终执行的 Txt 命令: {' '.join(command_txt)}")
            logger.debug(f"DEBUG: 最终执行的 Tsv 命令: {' '.join(command_tsv)}")

            creation_flags = 0
            if platform.system() == "Windows":
                try:
                    creation_flags = subprocess.CREATE_NO_WINDOW
                except AttributeError:
                    creation_flags = 0x08000000

            try:
                actual_timeout = timeout 
                logger.debug(f"DEBUG: Tesseract进程超时设置为: {actual_timeout} 秒。")
                
                # 在包含配置文件的目录中执行命令，以确保Tesseract能找到它
                process_cwd = os.path.dirname(temp_config_path) if temp_config_path else None

                process_text = subprocess.run(
                    command_txt, capture_output=True, timeout=actual_timeout,
                    creationflags=creation_flags, check=False, cwd=process_cwd
                )
                if process_text.returncode != 0:
                    stderr_msg = process_text.stderr.decode('utf-8', 'ignore').strip()
                    logger.error(f"ERROR: Tesseract纯文本命令执行失败，返回码: {process_text.returncode}, 错误输出: {stderr_msg}", exc_info=True)
                    return {"status": "error", "message": f"Tesseract纯文本命令执行失败，返回码: {process_text.returncode}，错误输出: {stderr_msg}"}

                process_data = subprocess.run(
                    command_tsv, capture_output=True, timeout=actual_timeout,
                    creationflags=creation_flags, check=False, cwd=process_cwd
                )
                if process_data.returncode != 0:
                    stderr_msg = process_data.stderr.decode('utf-8', 'ignore').strip()
                    logger.error(f"ERROR: Tesseract TSV命令执行失败，返回码: {process_data.returncode}, 错误输出: {stderr_msg}", exc_info=True)
                    return {"status": "error", "message": f"Tesseract TSV命令执行失败，返回码: {process_data.returncode}，错误输出: {stderr_msg}"}

            except subprocess.TimeoutExpired:
                logger.error(f"ERROR: Tesseract 子进程超时（超过 {timeout} 秒）。", exc_info=True)
                return {"status": "error", "message": f"Tesseract 子进程超时（超过 {timeout} 秒）。"}
            except FileNotFoundError:
                logger.error(f"ERROR: Tesseract 可执行文件未找到: '{tesseract_executable}'。", exc_info=True)
                return {"status": "error", "message": f"Tesseract 可执行文件未找到: '{tesseract_executable}'。请检查路径配置。"}
            except Exception as e:
                logger.error(f"ERROR: 执行Tesseract命令时发生未知错误: {str(e)}", exc_info=True)
                return {"status": "error", "message": f"执行Tesseract命令时发生未知错误: {str(e)}"}

            full_text = ""
            data_lines = []
            try:
                if os.path.exists(temp_output_txt):
                    with open(temp_output_txt, 'r', encoding='utf-8') as f:
                        full_text = f.read()
                if os.path.exists(temp_output_tsv):
                    with open(temp_output_tsv, 'r', encoding='utf-8') as f:
                        data_lines = f.read().strip().split('\n')

                data_dict = defaultdict(list)
                if len(data_lines) > 1:
                    header = data_lines[0].split('\t')
                    for line in data_lines[1:]:
                        values = line.split('\t')
                        if len(values) == len(header):
                            for h, v in zip(header, values):
                                data_dict[h].append(v)
                
                for key in ['level', 'page_num', 'block_num', 'par_num', 'line_num', 'word_num', 'left', 'top', 'width', 'height']:
                    if key in data_dict:
                        data_dict[key] = [int(v) for v in data_dict[key] if v.isdigit()]
                if 'conf' in data_dict:
                    data_dict['conf'] = [float(v) for v in data_dict['conf'] if v != '-1']

                return {"status": "success", "data": dict(data_dict), "full_text": full_text}
                
            except Exception as e:
                logger.error(f"ERROR: 读取或解析Tesseract结果文件失败: {str(e)}", exc_info=True)
                return {"status": "error", "message": f"读取或解析Tesseract结果文件失败: {str(e)}"}

        except Exception as e:
            logger.error(f"ERROR: _execute_tesseract_subprocess 外部主块发生意外错误: {str(e)}", exc_info=True)
            return {"status": "error", "message": f"Tesseract执行过程中出现意外错误: {str(e)}", "traceback": traceback.format_exc()}
        finally:
            for path in [temp_image_path, temp_output_txt, temp_output_tsv, temp_config_path]:
                if path and os.path.exists(path):
                    try:
                        os.remove(path)
                    except Exception as e:
                        logger.warning(f"WARNING: 无法清理临时文件 {path}: {e}")
    def set_tesseract_path(self, path: str):
        """设置Tesseract的可执行文件路径并验证"""
        try:
            import pytesseract
            if path and os.path.exists(path) and shutil.which(path):
                self.tesseract_path = path
                pytesseract.pytesseract.tesseract_cmd = path
                logger.info(f"已成功设置Tesseract路径: {path}")
                return True, "Tesseract路径设置成功"
            else:
                logger.warning(f"提供的Tesseract路径无效或不可执行: {path}")
                return False, "提供的路径无效或文件不存在或不可执行"
        except Exception as e:
            logger.error(f"设置Tesseract路径时发生错误: {e}")
            return False, f"设置路径时出错: {e}"

    def initialize(self, language: OCRLanguage = OCRLanguage.AUTO, 
               use_gpu: bool = False, **kwargs) -> Tuple[bool, str]:
        """
        初始化CVOCR模型 (V4.3 - 检测器逻辑修正版)。
        - 实例化 EnhancedTextDetector 作为支持自定义算法组合的主文本检测器。
        - PPOCRv3 模型仍然会按需加载，但主检测逻辑由 EnhancedTextDetector 驱动。
        """
        # ### 关键修正：在方法最开始就处理Tesseract路径 ###
        tesseract_path_from_config = self.config.get('tesseract_path')
        if tesseract_path_from_config:
            success, msg = self.set_tesseract_path(tesseract_path_from_config)
            if not success:
                self.logger_func(f"⚠️ 配置文件中的Tesseract路径无效: {tesseract_path_from_config}. {msg}", "WARNING")
        
        try:
            import pytesseract
        except ImportError:
            return False, "pytesseract未安装，请先安装: pip install pytesseract"
        
        if self.is_initialized:
            logger.info("CVOCR引擎已初始化，无需重复。")
            return True, "CVOCR引擎已初始化"

        # --- 核心逻辑修正：实例化 EnhancedTextDetector 作为主检测器 ---
        # 这将使GUI中的高级分割技术选项能够正常工作。
        try:
            self.text_detector = EnhancedTextDetector()
            logger.info("✅ 成功初始化支持自定义算法组合的 EnhancedTextDetector。")
        except Exception as e:
            logger.error(f"❌ 初始化 EnhancedTextDetector 失败: {e}", exc_info=True)
            return False, f"初始化 EnhancedTextDetector 失败: {e}"
        

        # 根据配置创建全元素检测器 (YOLO)
        try:
            self.unified_detector = UnifiedObjectDetector(
                logger_func=self.logger_func,
                cfg_path=self.config.get('yolo_cfg_path', 'yolov4-tiny.cfg'),
                weights_path=self.config.get('yolo_weights_path', 'yolov4-tiny.weights'),
                names_path=self.config.get('yolo_names_path', 'coco.names')
            )
            if self.unified_detector.net is None:
                self.unified_detector = None
        except Exception as e:
            self.unified_detector = None
            self.logger_func(f"❌ 初始化YOLO检测器时发生错误: {e}", "ERROR")

        # 检查AI库依赖
        try:
            import torch
            from transformers import (
                LayoutLMv2Processor, LayoutLMv2ForTokenClassification,
                TrOCRProcessor, VisionEncoderDecoderModel,
                GPT2Tokenizer, GPTNeoForCausalLM
            )
        except ImportError as e:
            logger.error(f"❌ 初始化失败：缺少必要的AI/图像处理库: {e}。", exc_info=True)
            return False, f"初始化失败：缺少必要的AI/图像处理库: {e}。请运行 'pip install torch transformers sentencepiece'"
        
        start_init_time = time.time()
        
        if use_gpu and torch.cuda.is_available():
            self.device = "cuda"
            logger.info("✅ 检测到可用GPU，将使用CUDA进行加速。")
        else:
            self.device = "cpu"
            if use_gpu:
                logger.warning("⚠️ 请求使用GPU，但未检测到可用的CUDA设备，将回退到CPU。")
            else:
                logger.info("ℹ️ 将使用CPU进行计算。")

        self.language = language
        
        logger.info(f"开始初始化CVOCR引擎 (语言: {language.value}, 精度: custom, 设备: {self.device})")
        
        success, message = self._initialize_tesseract()
        if not success:
            return False, message

        # 加载高级AI模型
        try:
            logger.info("ℹ️ FSRCNN功能已被移除，跳过加载。")
            
            if self.config.get('enable_layout_analysis', False):
                try:
                    self.layoutlm_processor = LayoutLMv2Processor.from_pretrained("microsoft/layoutlmv2-base-uncased")
                    self.layoutlm_model = LayoutLMv2ForTokenClassification.from_pretrained("microsoft/layoutlmv2-base-uncased").to(self.device)
                    self.layoutlm_model.eval()
                    logger.info("✅ LayoutLMv2模型加载成功。")
                except Exception as e:
                    self.layoutlm_model, self.layoutlm_processor = None, None
                    logger.error(f"❌ LayoutLMv2模型加载失败: {e}", exc_info=True)
            else:
                logger.info("ℹ️ LayoutLMv2未启用，跳过加载。")

            if self.config.get('enable_transformer_ocr', False):
                try:
                    model_name = self.config.get('transformer_ocr_model', 'microsoft/trocr-base-printed')
                    logger.info(f"正在加载指定的TrOCR模型: {model_name}")
                    self.trocr_processor = TrOCRProcessor.from_pretrained(model_name, use_fast=True)
                    self.trocr_model = VisionEncoderDecoderModel.from_pretrained(model_name, ignore_mismatched_sizes=True).to(self.device)
                    self.trocr_model.eval()
                    logger.info(f"✅ TrOCR模型 ({model_name}) 加载成功。")
                except Exception as e:
                    self.trocr_model, self.trocr_processor = None, None
                    logger.error(f"❌ TrOCR模型加载失败: {e}", exc_info=True)
            else:
                logger.info("ℹ️ TrOCR未启用，跳过加载。")

            if self.config.get('enable_context_analysis', False):
                try:
                    self.gpt_neo_tokenizer = GPT2Tokenizer.from_pretrained("EleutherAI/gpt-neo-125M")
                    self.gpt_neo_model = GPTNeoForCausalLM.from_pretrained("EleutherAI/gpt-neo-125M").to(self.device)
                    self.gpt_neo_model.eval()
                    self.gpt_neo_tokenizer.pad_token = self.gpt_neo_tokenizer.eos_token
                    logger.info("✅ GPT-Neo模型加载成功。")
                except Exception as e:
                    self.gpt_neo_model, self.gpt_neo_tokenizer = None, None
                    logger.error(f"❌ GPT-Neo模型加载失败: {e}", exc_info=True)
            else:
                logger.info("ℹ️ GPT-Neo未启用，跳过加载。")

        except Exception as e:
            logger.error(f"❌ 加载高级AI模型时发生外部意外错误: {e}", exc_info=True)
            return False, f"加载高级AI模型时发生意外错误: {e}。请检查网络连接和磁盘空间。"

        init_time = time.time() - start_init_time
        self.is_initialized = True

        self.version_info = {
            'cvocr_version': CVOCRConstants.VERSION,
            'python': sys.version.split()[0],
            'tesseract': CVOCRVersionManager.get_tesseract_version(self.tesseract_path),
            'transformers': CVOCRVersionManager.get_transformers_version(),
            'opencv': CVOCRVersionManager.get_opencv_version(),
            'torch': CVOCRVersionManager.get_torch_version(),
            'language': language.value,
            'use_gpu': self.device == "cuda",
            'device': self.device,
            'init_time': init_time,
            'config': self.config.copy(),
            'components': {
                'tesseract_enabled': True,
                'fsrcnn_enabled': False,
                'layoutlm_enabled': self.config.get('enable_layout_analysis', False) and (self.layoutlm_model is not None),
                'gpt_neo_enabled': self.config.get('enable_context_analysis', False) and (self.gpt_neo_model is not None),
                'transformer_ocr_enabled': self.config.get('enable_transformer_ocr', False) and (self.trocr_model is not None)
            },
            'system_info': CVOCRVersionManager.get_system_info(),
            'initialization_timestamp': datetime.now().isoformat()
        }
        
        test_success, test_msg = self._test_ocr_engine()
        if not test_success:
            self.is_initialized = False
            return False, f"CVOCR引擎初始化成功，但Tesseract基础测试失败: {test_msg}"
        
        success_message = f"CVOCR引擎初始化成功：语言: {language.value}, 精度: custom, 耗时: {init_time:.2f}秒"
        logger.info(f"{success_message}, AI设备: {self.device}")
        return True, success_message
    
    
    
    
    def _initialize_tesseract(self) -> Tuple[bool, str]:
        """初始化Tesseract OCR (V3.4 语言包检查增强版)"""
        try:
            import pytesseract
            
            # --- 关键修正：在所有操作前，优先确定并设置Tesseract可执行文件路径 ---
            # 检查 self.tesseract_path (该路径由 initialize 方法或 set_tesseract_path 方法设置)。
            # 如果这个路径有效存在，就将其明确地应用到 pytesseract 库的全局命令变量中。
            # 这样，后续所有对 pytesseract 的调用（如 get_tesseract_version）都会使用这个正确的路径。
            if self.tesseract_path and os.path.exists(self.tesseract_path):
                pytesseract.pytesseract.tesseract_cmd = self.tesseract_path
            
            # 现在可以安全地调用版本检查，它会优先使用上面设置的路径
            try:
                version = pytesseract.get_tesseract_version()
                logger.info(f"Tesseract OCR引擎可用，版本: {version}")
            except Exception as e:
                logger.error(f"❌ Tesseract 可执行文件无法运行或版本检测失败: {e}", exc_info=True)
                return False, f"Tesseract 可执行文件无法运行或版本检测失败: {e}"

            # --- 修正：移除多余的参数 ---
            # _get_tesseract_config 方法现在从 self.config 读取所有设置，
            # 不再需要从外部传入参数。
            tesseract_config_str = self._get_tesseract_config()
            self.tesseract_config = tesseract_config_str
            
            requested_langs = self.config['lang'].split('+')
            
            # 使用 pytesseract.pytesseract.tesseract_cmd 作为唯一的真理来源，简化路径判断
            tesseract_executable_for_subprocess = pytesseract.pytesseract.tesseract_cmd

            try:
                available_langs_output = subprocess.run([tesseract_executable_for_subprocess, '--list-langs'], capture_output=True, text=True, check=True)
                available_langs = set(line.strip() for line in available_langs_output.stdout.splitlines() if line.strip() and not line.strip().startswith('tesseract'))
                
                missing_langs = [lang for lang in requested_langs if lang not in available_langs]
                
                message = f"Tesseract初始化成功，版本: {version}"
                if missing_langs:
                    logger.warning(f"⚠️ 缺少Tesseract语言包: {', '.join(missing_langs)}。请安装。")
                    if not any(lang in available_langs for lang in requested_langs):
                        return False, f"Tesseract缺少所有请求的语言包: {', '.join(requested_langs)}。请安装。"
                    else:
                        message += f" (警告: 缺少语言包 {', '.join(missing_langs)})"
            except FileNotFoundError:
                logger.error(f"❌ Tesseract可执行文件 '{tesseract_executable_for_subprocess}' 未找到，无法检查语言包。", exc_info=True)
                return False, f"Tesseract可执行文件 '{tesseract_executable_for_subprocess}' 未找到，无法检查语言包。"
            except subprocess.CalledProcessError as e:
                logger.error(f"❌ Tesseract --list-langs 命令执行失败: {e.stderr}", exc_info=True)
                return False, f"Tesseract --list-langs 命令执行失败: {e.stderr}"
            except Exception as e:
                logger.error(f"❌ 检查Tesseract语言包时发生意外错误: {e}", exc_info=True)
                return False, f"检查Tesseract语言包时发生意外错误: {e}"
            
            return True, message
                
        except ImportError:
            logger.error("❌ pytesseract未安装，请安装: pip install pytesseract", exc_info=True)
            return False, "pytesseract未安装，请安装: pip install pytesseract"
        except Exception as e:
            logger.error(f"❌ Tesseract初始化失败: {e}", exc_info=True)
            return False, f"Tesseract初始化失败: {str(e)}"
    def _get_tesseract_config(self, lang_override: Optional[str] = None, psm_override: Optional[int] = None) -> List[Tuple[str, str]]:
        """
        根据UI设置构建Tesseract配置列表 (V4.8 - 支持PSM覆盖版)。
        返回一个配置元组列表，每个元组是 (配置字符串, 描述)。
        """
        # --- PSM (页面分割模式) ---
        if psm_override is not None:
            psm_val = str(psm_override)
        else:
            psm_value_from_config = self.config.get('psm', '6')
            if isinstance(psm_value_from_config, str):
                psm_val = psm_value_from_config.split(':')[0].strip()
            else:
                psm_val = str(psm_value_from_config)

        # --- OEM (引擎模式) ---
        selected_oems = self.config.get('oem_options', {'3': True})
        enabled_oem_keys = [key for key, enabled in selected_oems.items() if enabled]
        
        oem_defs = {
            '0': "经典引擎", '1': "神经网络(LSTM)", 
            '2': "经典+LSTM", '3': "默认(推荐LSTM)"
        }
        
        # 语言
        lang_code = lang_override if lang_override else self.config.get('lang', 'chi_sim+eng')

        # 【关键】基础额外配置（包含中文优化）
        extra_configs = []
        if 'chi_sim' in lang_code or 'chi_tra' in lang_code:
            extra_configs.extend([
                '-c textord_tabfind_find_tables=1',
                '-c chopper_enable=0',
                '-c preserve_interword_spaces=1',
                '-c language_model_penalty_non_freq_dict_word=0.1',
                '-c language_model_penalty_non_dict_word=0.15',
            ])
        extra_config_str = ' '.join(extra_configs)
        
        configs_to_run = []

        if not enabled_oem_keys:
            desc = f"运行: PSM={psm_val}, OEM=Tesseract默认"
            config_str = f'--psm {psm_val} -l {lang_code} {extra_config_str}'
            configs_to_run.append((config_str.strip(), desc))
        else:
            for oem_key in enabled_oem_keys:
                desc = f"运行: PSM={psm_val}, OEM={oem_key} ({oem_defs[oem_key]})"
                config_str = f'--psm {psm_val} --oem {oem_key} -l {lang_code} {extra_config_str}'
                configs_to_run.append((config_str.strip(), desc))
        
        # self.config的更新保持不变
        self.config['psm_val'] = psm_val
        self.config['lang'] = lang_code
        
        return configs_to_run
    
    
    def _test_ocr_engine(self) -> Tuple[bool, str]:
        """测试OCR引擎 (仅测试Tesseract基础功能)"""
        try:
            test_img = np.ones((100, 400, 3), dtype=np.uint8) * 255
            cv2.putText(test_img, 'CVOCR Test 2025', (50, 50), cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 0, 0), 2)
            test_pil_img = Image.fromarray(cv2.cvtColor(test_img, cv2.COLOR_BGR2RGB))
            
            tesseract_result = self._execute_tesseract_subprocess(
                image_pil=test_pil_img, tesseract_cmd_path=self.tesseract_path,
                config_str=self.tesseract_config, timeout=self.config.get('tesseract_process_timeout', 300)
            )
            if tesseract_result['status'] == 'error':
                logger.error(f"OCR引擎测试失败 (Tesseract子进程错误): {tesseract_result['message']}")
                return False, f"OCR引擎测试失败: {tesseract_result['message']}"

            result = tesseract_result['full_text']
            
            if any(word in result.upper() for word in ['CVOCR', 'TEST', '2025']):
                return True, f"OCR引擎测试通过，识别结果: {result.strip()}"
            else:
                return True, f"OCR引擎可用，测试结果: {result.strip()}"
                
        except Exception as e:
            logger.error(f"OCR引擎测试失败: {e}", exc_info=True)
            return False, f"OCR引擎测试异常: {str(e)}"
    
    def _run_segmentation_and_recognize(self, image_np: np.ndarray, scale_factors: Tuple[float, float], regions: List[np.ndarray]) -> Tuple[Dict, str]:
        """
        【增强版】对每个已检测区域进行识别 (V4.9 - 中文识别修正版)
        - 调用增强的配置生成函数，确保在使用高级分割时，为Tesseract传入正确的PSM模式和所有必需的中文优化参数。
        - 修复了在高级分割流程中无法正确识别中文的问题。
        - 保持了对TransformerOCR作为区域识别引擎的支持。
        - 保持了已修复的、宏观准确的坐标系关联逻辑。
        """
        if not regions: 
            logger.warning("识别流程中止：没有从上游检测器接收到任何文本区域。")
            return {}, ""

        logger.info(f"🚀 开始对 {len(regions)} 个已检测区域进行识别... 缩放比例: x={scale_factors[0]:.2f}, y={scale_factors[1]:.2f}")
        
        recognizer_engine = self.config.get('segmentation_recognizer', 'Tesseract')
        logger.info(f"将使用 '{recognizer_engine}' 引擎进行识别。")
        
        all_ocr_data = defaultdict(list)
        recognized_parts = []
        scale_x, scale_y = scale_factors

        if recognizer_engine == "TransformerOCR" and self.trocr_model:
            self.performance_stats['component_usage']['transformer_ocr'] += 1
            region_images_for_trocr = []
            valid_region_boxes = []

            for region_box in regions:
                try:
                    rect = cv2.minAreaRect(region_box)
                    center, (width, height), angle = rect

                    # --- 最终版智能旋转逻辑 ---
                    if width < height:
                        width, height = height, width
                        swapped = True
                    else:
                        swapped = False

                    aspect_ratio = width / height if height > 0 else 0
                    if swapped and aspect_ratio > 1.5:
                        angle += 90
                    # --- 逻辑结束 ---

                    if width <= 5 or height <= 5: continue
                    width, height = int(width), int(height)

                    M = cv2.getRotationMatrix2D(center, angle, 1.0)
                    warped_bgr = cv2.warpAffine(image_np, M, (image_np.shape[1], image_np.shape[0]), flags=cv2.INTER_CUBIC, borderMode=cv2.BORDER_REPLICATE)
                    cropped_bgr = cv2.getRectSubPix(warped_bgr, (width, height), center)
                    if cropped_bgr is None or cropped_bgr.size == 0: continue
                    
                    region_images_for_trocr.append(cropped_bgr)
                    valid_region_boxes.append(region_box)
                except Exception as e:
                    logger.warning(f"处理区域以准备TrOCR输入时出错: {e}")

            if region_images_for_trocr:
                trocr_results = self._apply_transformer_ocr(region_images_for_trocr)
                for i, result in enumerate(trocr_results):
                    if result.get('error') or not result['text'].strip(): continue
                    
                    region_box = valid_region_boxes[i]
                    x_coords, y_coords = region_box[:, 0], region_box[:, 1]
                    x_start, y_start = int(np.min(x_coords)), int(np.min(y_coords))
                    width, height = int(np.max(x_coords) - x_start), int(np.max(y_coords) - y_start)
                    
                    all_ocr_data['left'].append(int(x_start * scale_x))
                    all_ocr_data['top'].append(int(y_start * scale_y))
                    all_ocr_data['width'].append(int(width * scale_x))
                    all_ocr_data['height'].append(int(height * scale_y))
                    all_ocr_data['text'].append(result['text'])
                    all_ocr_data['conf'].append(result['confidence'])
                    all_ocr_data['word_num'].append(len(result['text'].split()))
                    all_ocr_data['line_num'].append(1)
                    all_ocr_data['par_num'].append(1)
                    all_ocr_data['block_num'].append(i + 1)
                    
                    recognized_parts.append({'text': result['text'], 'y_coord': int(y_start * scale_y), 'x_coord': int(x_start * scale_x)})
        else:
            if recognizer_engine == "TransformerOCR":
                logger.warning("TrOCR被选为识别引擎，但模型未加载。将自动回退到Tesseract。")
            self.performance_stats['component_usage']['tesseract'] += 1
            tesseract_timeout = self.config.get('tesseract_process_timeout', 300)
            
            use_fine_tuning = self.config.get('enable_tesseract_fine_tuning', True)
            if use_fine_tuning:
                logger.info("Tesseract精细化预处理已启用。")
            else:
                logger.info("Tesseract精细化预处理已禁用。")
            
            # 【核心修正】: 调用增强的配置生成函数，并传入从GUI解析的PSM值
            psm_str_from_gui = self.settings['psm_mode'].get()
            psm_val = int(psm_str_from_gui.split(':')[0].strip())

            # 调用中央配置函数，并覆盖PSM值，以获得包含所有优化（包括中文）的完整配置
            configs_list = self._get_tesseract_config(psm_override=psm_val)
            tesseract_config_for_regions = configs_list[0][0] if configs_list else ""
            
            # 更新日志，使其准确反映正在使用的配置
            logger.info(f"所有区域将使用配置: '{tesseract_config_for_regions}'")
            logger.warning(f"当前使用的PSM模式为 '{psm_str_from_gui}'。如果识别效果不佳，"
                           f"请确保此模式适合处理已分割的独立文本块（推荐使用PSM 6, 7, 8, 13等）。")

            for i, region_box in enumerate(regions):
                try:
                    rect = cv2.minAreaRect(region_box)
                    center, (width, height), angle = rect

                    # 智能旋转逻辑
                    if width < height:
                        width, height = height, width
                        swapped = True
                    else:
                        swapped = False
                    aspect_ratio = width / height if height > 0 else 0
                    if swapped and aspect_ratio > 1.5: angle += 90
                    
                    if width <= 5 or height <= 5: continue
                    width, height = int(width), int(height)

                    # 切割并校正区域
                    M = cv2.getRotationMatrix2D(center, angle, 1.0)
                    warped_bgr = cv2.warpAffine(image_np, M, (image_np.shape[1], image_np.shape[0]), flags=cv2.INTER_CUBIC, borderMode=cv2.BORDER_REPLICATE)
                    cropped_bgr = cv2.getRectSubPix(warped_bgr, (width, height), center)
                    if cropped_bgr is None or cropped_bgr.size == 0: continue
                    
                    # 应用精细化预处理（如果启用）
                    processed_for_ocr = cropped_bgr
                    if use_fine_tuning:
                        gray_cropped = cv2.cvtColor(cropped_bgr, cv2.COLOR_BGR2GRAY)
                        h_proc, _ = gray_cropped.shape
                        if h_proc > 0 and (h_proc < 24 or h_proc > 64):
                            scale = 40.0 / h_proc
                            gray_cropped = cv2.resize(gray_cropped, (0,0), fx=scale, fy=scale, interpolation=cv2.INTER_CUBIC)
                        clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(4, 4))
                        enhanced = clahe.apply(gray_cropped)
                        _, binarized = cv2.threshold(enhanced, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
                        bordered = cv2.copyMakeBorder(binarized, 8, 8, 8, 8, cv2.BORDER_CONSTANT, value=[255])
                        processed_for_ocr = cv2.cvtColor(bordered, cv2.COLOR_GRAY2BGR)
                    
                    cropped_pil = Image.fromarray(cv2.cvtColor(processed_for_ocr, cv2.COLOR_BGR2RGB))
                    
                    # 调用Tesseract
                    region_result = self._execute_tesseract_subprocess(
                        image_pil=cropped_pil, tesseract_cmd_path=self.tesseract_path,
                        config_str=tesseract_config_for_regions, timeout=tesseract_timeout
                    )
                    
                    if region_result["status"] == "success" and region_result.get("full_text", "").strip():
                        full_text_from_region = region_result.get("full_text", "").strip()
                        
                        x, y, w, h = cv2.boundingRect(region_box.astype(np.int32))
                        
                        confidences = region_result.get("data", {}).get("conf", [])
                        avg_conf = sum(confidences) / len(confidences) if confidences else 95.0

                        all_ocr_data['left'].append(int(x * scale_x))
                        all_ocr_data['top'].append(int(y * scale_y))
                        all_ocr_data['width'].append(int(w * scale_x))
                        all_ocr_data['height'].append(int(h * scale_y))
                        all_ocr_data['text'].append(full_text_from_region)
                        all_ocr_data['conf'].append(avg_conf)
                        
                        all_ocr_data['word_num'].append(len(full_text_from_region.split()))
                        all_ocr_data['line_num'].append(i + 1)
                        all_ocr_data['par_num'].append(i + 1)
                        all_ocr_data['block_num'].append(i + 1)
                        
                        recognized_parts.append({
                            'text': full_text_from_region, 
                            'y_coord': int(y * scale_y), 
                            'x_coord': int(x * scale_x)
                        })

                except Exception as e:
                    logger.warning(f"处理区域 {i} 时发生错误: {e}")
                    continue

        # 按阅读顺序对所有识别出的文本片段进行排序
        recognized_parts.sort(key=lambda item: (item['y_coord'], item['x_coord']))
        final_full_text = "\n".join([part['text'] for part in recognized_parts])

        return dict(all_ocr_data), final_full_text
    
    
    
    def _calculate_bbox_iou_for_polygons(self, poly1, poly2) -> float:
        """计算两个多边形区域的交并比(IoU)"""
        try:
            r1 = cv2.boundingRect(poly1.astype(int))
            r2 = cv2.boundingRect(poly2.astype(int))
            
            max_x = max(r1[0]+r1[2], r2[0]+r2[2])
            max_y = max(r1[1]+r1[3], r2[1]+r2[3])
            
            img1 = np.zeros((max_y, max_x), dtype=np.uint8)
            img2 = np.zeros((max_y, max_x), dtype=np.uint8)

            cv2.fillPoly(img1, [poly1.astype(int)], 255)
            cv2.fillPoly(img2, [poly2.astype(int)], 255)
            
            intersection = np.sum(cv2.bitwise_and(img1, img2) > 0)
            union = np.sum(cv2.bitwise_or(img1, img2) > 0)
            
            return intersection / union if union > 0 else 0.0
        except Exception:
            return 0.0
    def _merge_blocks_by_layoutlm(self, ocr_data: Dict, layout_info: Dict) -> Dict:
        """
        使用LayoutLMv2的分析结果，对OCR文本块进行语义合并。
        
        Args:
            ocr_data (Dict): 包含多个'text_blocks'的原始OCR结果。
            layout_info (Dict): 来自LayoutLMv2的布局分析结果。

        Returns:
            Dict: 合并后的新的OCR结果字典。
        """
        self.logger_func("🧠 开始执行基于LayoutLMv2的语义合并...", "INFO")
        if not ocr_data.get('text_blocks') or not layout_info.get('text_regions'):
            self.logger_func("⚠️ 语义合并中止：缺少OCR文本块或LayoutLMv2分析结果。", "WARNING")
            return ocr_data

        # 1. 为每个原始OCR块匹配一个LayoutLMv2的语义标签
        ocr_blocks = ocr_data['text_blocks']
        for block in ocr_blocks:
            # _match_text_to_layout 会返回 {'region_type': 'Paragraph', ...}
            block['layout_info'] = self._match_text_to_layout(block, layout_info)

        # 2. 按语义标签和空间位置进行分组
        # 我们只合并被标记为 'Paragraph', 'List', 'Table' 的块
        mergeable_tags = {'Paragraph', 'List', 'Table', 'Section-header'}
        
        merged_blocks = []
        processed_indices = set()
        
        # 按阅读顺序排序
        ocr_blocks.sort(key=lambda b: (b['bbox'][1], b['bbox'][0]))

        for i in range(len(ocr_blocks)):
            if i in processed_indices:
                continue

            current_block = ocr_blocks[i]
            current_tag = current_block.get('layout_info', {}).get('region_type', 'unknown')

            # 如果当前块不可合并，或没有标签，则直接保留
            if current_tag not in mergeable_tags:
                merged_blocks.append(current_block)
                processed_indices.add(i)
                continue

            # 创建一个新的合并组
            merge_group = [current_block]
            processed_indices.add(i)

            # 向后查找可以合并到此组的其他块
            for j in range(i + 1, len(ocr_blocks)):
                if j in processed_indices:
                    continue
                
                next_block = ocr_blocks[j]
                next_tag = next_block.get('layout_info', {}).get('region_type', 'unknown')

                # 合并条件：语义标签相同，且在空间上是连续的
                if next_tag == current_tag:
                    # 简单的空间连续性判断：下一个块的左上角Y坐标与当前组的
                    # 最后一个块的左下角Y坐标相差不大（在一个行高内）
                    last_block_in_group = merge_group[-1]
                    y_gap = next_block['bbox'][1] - last_block_in_group['bbox'][3]
                    line_height = last_block_in_group['bbox'][3] - last_block_in_group['bbox'][1]
                    
                    if y_gap < line_height: # 垂直间隙小于一个行高
                        merge_group.append(next_block)
                        processed_indices.add(j)

            # 3. 将合并组中的所有块聚合成一个大块
            if len(merge_group) > 1:
                # 合并文本
                full_text = "\n".join([b['text'] for b in merge_group])
                # 合并边界框
                min_x = min(b['bbox'][0] for b in merge_group)
                min_y = min(b['bbox'][1] for b in merge_group)
                max_x = max(b['bbox'][2] for b in merge_group)
                max_y = max(b['bbox'][3] for b in merge_group)
                
                # 计算合并后的平均置信度
                avg_conf = np.mean([b['confidence'] for b in merge_group])

                merged_block = {
                    'text': full_text,
                    'confidence': int(avg_conf),
                    'bbox': [min_x, min_y, max_x, max_y],
                    'word_num': len(full_text.split()),
                    'line_num': len(full_text.split('\n')),
                    'par_num': 1, # 整个组合并成一个段落
                    'block_num': merge_group[0]['block_num'],
                    'layout_info': {'region_type': f"Merged-{current_tag}"}
                }
                merged_blocks.append(merged_block)
                self.logger_func(f"  -> 成功将 {len(merge_group)} 个 '{current_tag}' 块合并。", "DEBUG")
            else:
                # 如果组里只有一个块，直接保留
                merged_blocks.append(current_block)

        # 4. 构建新的 ocr_data
        new_ocr_data = ocr_data.copy()
        new_ocr_data['text_blocks'] = merged_blocks
        new_ocr_data['full_text'] = "\n\n".join([b['text'] for b in merged_blocks])
        new_ocr_data['total_blocks'] = len(merged_blocks)
        
        self.logger_func(f"🧠 语义合并完成，文本块从 {len(ocr_blocks)} 个减少到 {len(merged_blocks)} 个。", "SUCCESS")
        return new_ocr_data        
    def recognize_text_enhanced(self, image_path: str, enable_preprocessing: bool = True) -> Tuple[Optional[Dict], str]:
        """
        CVOCR增强文本识别的核心实现 (V4.9 - LayoutLMv2语义合并集成版)
        - 新增一个基于LayoutLMv2的语义合并分支，在所有识别和分析完成后执行。
        - 根据用户的GUI选择，在纯几何合并和高级语义合并之间进行切换。
        - 确保在调用语义合并前，所有必要的数据（初步OCR结果、LayoutLMv2分析）都已准备就绪。
        """
        recognition_start_time = time.time()
        
        try:
            # --- 步骤 1: 初始化统计和配置 ---
            self.performance_stats['total_recognitions'] += 1
            
            # --- 步骤 2: 图像预处理 (统一入口) ---
            self.logger_func("工作流步骤1: 正在应用统一的图像预处理...", "INFO")
            image_processor = AdvancedTextImageProcessor()
            processed_image_np, preprocess_msg, metadata = image_processor.intelligent_preprocess_image(
                image_path, **self.config
            )
            if processed_image_np is None:
                self._update_failed_stats()
                return None, f"图像预处理失败: {preprocess_msg}"
            
            # 计算坐标转换比例
            try:
                with Image.open(image_path) as img:
                    original_width, original_height = img.size
            except Exception as e:
                self._update_failed_stats()
                return None, f"无法读取原始图像尺寸: {e}"

            processed_height, processed_width = processed_image_np.shape[:2]
            scale_x = original_width / processed_width if processed_width > 0 else 1.0
            scale_y = original_height / processed_height if processed_height > 0 else 1.0

            # --- 步骤 3: 文本与元素检测 (根据模式选择) ---
            text_regions = []
            shape_blocks = []

            # 【核心修正】: 检查是否为快速模式
            is_quick_mode = self.config.get('quick_mode', False)
            
            if is_quick_mode:
                # 工作流 C: 快速模式
                self.logger_func("工作流步骤2: 模式[快速OCR] -> 跳过文本检测，直接进行整页识别...", "INFO")
                # 在这种模式下，我们不需要检测区域，所以 text_regions 保持为空列表
                # 后续的识别逻辑将直接处理整张图片
            
            else:
                is_full_element_mode = self.config.get('enable_advanced_segmentation', False)

                if is_full_element_mode:
                    # 工作流 A: 全元素检测模式
                    self.logger_func("工作流步骤2: 模式[全元素检测] -> 正在使用YOLO进行检测...", "INFO")
                    if self.unified_detector and self.unified_detector.net:
                        self.performance_stats['component_usage']['unified_detector'] += 1
                        all_detected_objects = self.unified_detector.detect_all_objects(processed_image_np)
                        
                        for obj in all_detected_objects:
                            x1, y1, x2, y2 = obj['bbox']
                            if obj['label'] in ['text', 'table']:
                                points = np.array([[x1, y1], [x2, y1], [x2, y2], [x1, y2]], dtype=np.float32)
                                text_regions.append(points)
                            else:
                                shape_blocks.append({
                                    'text': f"[{obj['label'].upper()}]", 'confidence': int(obj['confidence'] * 100),
                                    'bbox': obj['bbox'], 'is_shape': True,
                                    'word_num': 1, 'line_num': 1, 'par_num': 1, 'block_num': 999 
                                })
                        self.logger_func(f"YOLO检测到 {len(text_regions)} 个文本/表格区域和 {len(shape_blocks)} 个图形。", "INFO")
                    else:
                        self.logger_func("⚠️ 全元素检测模式已启用，但YOLO检测器未加载。", "WARNING")
                else:
                    # 工作流 B: 纯文本OCR模式
                    self.logger_func("工作流步骤2: 模式[纯文本OCR] -> 正在使用高级分割技术进行检测...", "INFO")
                    self.performance_stats['component_usage']['advanced_segmentation'] += 1
                    enabled_algorithms = self.config.get('enabled_segmentation_algorithms', [])
                    self.text_detector.config.update(self.config)
                    
                    text_regions, _ = self.text_detector.detect_text_regions_advanced(
                        processed_image_np, enabled_algorithms
                    )
                    self.logger_func(f"高级分割技术检测到 {len(text_regions)} 个文本区域。", "INFO")

            # --- 步骤 4: 区域的初步识别 (或整页识别) ---
            # 【核心修正】: 根据是否为快速模式，选择不同的识别策略
            if is_quick_mode:
                self.logger_func("工作流步骤3: 将整张预处理后的图片送入Tesseract进行端到端识别...", "INFO")
                
                # 直接调用 Tesseract 处理整张图片
                full_image_pil = Image.fromarray(cv2.cvtColor(processed_image_np, cv2.COLOR_BGR2RGB))
                tesseract_configs = self._get_tesseract_config() # 获取为快速模式配置的 --psm 3 等参数
                
                # 直接执行 Tesseract 并获取结果
                tesseract_result = self._execute_tesseract_subprocess(
                    image_pil=full_image_pil,
                    tesseract_cmd_path=self.tesseract_path,
                    config_str=tesseract_configs,
                    timeout=self.config.get('tesseract_process_timeout', 300)
                )

                if tesseract_result['status'] == 'success':
                    ocr_data = tesseract_result['data']
                    full_text = tesseract_result['full_text']
                    # 将 Tesseract 返回的块级坐标应用缩放
                    for key in ['left', 'top', 'width', 'height']:
                        if key in ocr_data:
                            ocr_data[key] = [int(v * (scale_x if key in ['left', 'width'] else scale_y)) for v in ocr_data[key]]
                else:
                    raise CVOCRException(f"Tesseract在快速模式下执行失败: {tesseract_result.get('message', '未知错误')}")
            else:
                # 原始逻辑：对分割出的区域进行识别
                self.logger_func(f"工作流步骤3: 将 {len(text_regions)} 个区域送入识别引擎进行初步识别...", "INFO")
                ocr_data, full_text = self._run_segmentation_and_recognize(
                    processed_image_np, (scale_x, scale_y), text_regions
                )

            # --- 步骤 5: AI分析 (为语义合并和最终结果做准备) ---
            self.logger_func("工作流步骤4: 正在执行AI分析...", "INFO")
            layout_info, context_info, transformer_results = None, None, None
            
            # LayoutLMv2 必须在语义合并前运行
            if (self.config.get('enable_layout_analysis', False) or self.config.get('enable_layoutlm_merge', False)) and self.layoutlm_model:
                layout_info = self._analyze_layout_with_layoutlmv2(processed_image_np)
                self.performance_stats['component_usage']['layoutlmv2'] += 1

            if self.config.get('enable_context_analysis', False) and full_text and self.gpt_neo_model:
                full_text, context_info = self._analyze_context_with_gpt_neo(full_text, ocr_data or {})
                self.performance_stats['component_usage']['gpt_neo'] += 1

            
            
            # --- 步骤 6: 最终结果整合 (包含语义合并分支) ---
            self.logger_func("工作流步骤5: 正在整合最终结果...", "INFO")
            # 检查是否需要执行高级语义合并
            if (self.config.get('enable_smart_line_merge') and 
                self.config.get('enable_layoutlm_merge') and 
                layout_info and not layout_info.get('error')):
                
                # 6a. 先进行一次常规的后处理，得到待合并的文本块
                initial_results = self._post_process_cvocr_results(
                    ocr_data, full_text, 
                    layout_info, context_info, transformer_results, metadata,
                    shape_blocks=shape_blocks
                )
                
                # 6b. 调用新的语义合并方法
                final_results_dict = self._merge_blocks_by_layoutlm(initial_results, layout_info)

                # 更新 full_text 以反映合并后的结果
                full_text = final_results_dict['full_text']
            else:
                # 6c. 如果不使用语义合并，则走原来的常规后处理流程
                if self.config.get('enable_layoutlm_merge'):
                    self.log_message("⚠️ 请求了语义合并，但LayoutLMv2未启用或分析失败，回退到几何合并。", "WARNING")
                
                final_results_dict = self._post_process_cvocr_results(
                    ocr_data, full_text, 
                    layout_info, context_info, transformer_results, metadata,
                    shape_blocks=shape_blocks
                )

            # --- 步骤 7: 生成摘要并返回 ---
            processing_time = time.time() - recognition_start_time
            self._update_success_stats(processing_time)
            summary_msg = self._generate_cvocr_result_summary(final_results_dict, processing_time, preprocess_msg)
            final_results_dict['processing_metadata']['total_processing_time'] = processing_time
            
            return final_results_dict, summary_msg

        except Exception as e:
            self._update_failed_stats()
            error_message = f"在recognize_text_enhanced主流程中发生严重错误: {str(e)}"
            self.logger_func(f"❌ {error_message}\n{traceback.format_exc()}", "ERROR")
            return None, error_message
        finally:
            self.logger_func("识别流程结束。", "DEBUG")
    def _apply_fsrcnn_enhancement(self, image: np.ndarray) -> np.ndarray:
        """
        应用真正的FSRCNN超分辨率增强 (V3.29 DBNet兼容修正版)
        """
        # FSRCNN功能已被移除，此函数仅为保留结构，直接返回原图
        if self.config.get('enable_super_resolution', False):
             logger.warning("FSRCNN功能已被移除，超分辨率增强将不会执行。")
        return image
    
    def _analyze_layout_with_layoutlmv2(self, image: np.ndarray) -> Dict:
        """使用真正的LayoutLMv2进行文档布局分析。"""
        import torch
        from transformers import LayoutLMv2Processor, LayoutLMv2ForTokenClassification

        if not self.layoutlm_model or not self.layoutlm_processor:
            logger.warning("LayoutLMv2模型或处理器未加载，无法进行布局分析。")
            return {'error': 'LayoutLMv2模型未加载', 'text_regions': []}

        try:
            pil_image = Image.fromarray(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
            
            # 准备模型输入
            encoding = self.layoutlm_processor(pil_image, return_tensors="pt").to(self.device)
            
            # 模型推理
            with torch.no_grad():
                outputs = self.layoutlm_model(**encoding)
            
            # 解析预测结果
            predictions = outputs.logits.argmax(-1).squeeze().tolist()
            token_boxes = encoding.bbox.squeeze().tolist()
            tokens = self.layoutlm_processor.tokenizer.convert_ids_to_tokens(encoding.input_ids.squeeze().tolist())
            
            text_regions = []
            for i, pred in enumerate(predictions):
                if pred == 0 or tokens[i] in ['[CLS]', '[SEP]', '[PAD]']:
                    continue

                box = token_boxes[i]
                text_regions.append({
                    'text': tokens[i],
                    'bbox': [box[0], box[1], box[2], box[3]], # x_min, y_min, x_max, y_max
                    'type_id': pred,
                    'type_name': self.layoutlm_model.config.id2label.get(pred, 'UNKNOWN'),
                    'confidence': float(torch.softmax(outputs.logits, dim=-1).squeeze()[i][pred].item())
                })
            
            aggregated_regions = self._aggregate_layoutlmv2_regions(text_regions, image.shape[1], image.shape[0])

            layout_analysis = {
                'text_regions': aggregated_regions,
                'document_structure': {
                    'estimated_language': 'mixed',
                    'text_density': 'medium'
                },
                'confidence_score': float(torch.softmax(outputs.logits, dim=-1).max().item()),
            }
            
            logger.info(f"LayoutLMv2布局分析完成，检测到 {len(aggregated_regions)} 个聚合文本区域。")
            return layout_analysis
        except Exception as e:
            logger.error(f"LayoutLMv2布局分析失败: {e}\n{traceback.format_exc()}")
            return {'error': str(e), 'text_regions': []}
    
    def _aggregate_layoutlmv2_regions(self, regions: List[Dict], image_width: int, image_height: int) -> List[Dict]:
        """
        聚合LayoutLMv2输出的token级区域，形成更粗粒度的文本块。
        """
        aggregated_output = []
        
        def scale_box(box):
            return [
                int(box[0] / 1000 * image_width),
                int(box[1] / 1000 * image_height),
                int(box[2] / 1000 * image_width),
                int(box[3] / 1000 * image_height)
            ]

        regions.sort(key=lambda r: (r['bbox'][1], r['bbox'][0], r['type_id']))

        current_block = None
        for region in regions:
            scaled_bbox = scale_box(region['bbox'])
            if current_block is None:
                current_block = {
                    'text': region['text'], 'bbox': scaled_bbox, 'type_name': region['type_name'],
                    'type_id': region['type_id'], 'confidence': region['confidence'], 'count': 1
                }
            else:
                overlap_threshold = 20
                if region['type_id'] == current_block['type_id'] and \
                   abs(scaled_bbox[1] - current_block['bbox'][1]) < overlap_threshold:
                    
                    current_block['text'] += " " + region['text']
                    current_block['bbox'][0] = min(current_block['bbox'][0], scaled_bbox[0])
                    current_block['bbox'][1] = min(current_block['bbox'][1], scaled_bbox[1])
                    current_block['bbox'][2] = max(current_block['bbox'][2], scaled_bbox[2])
                    current_block['bbox'][3] = max(current_block['bbox'][3], scaled_bbox[3])
                    current_block['confidence'] = (current_block['confidence'] * current_block['count'] + region['confidence']) / (current_block['count'] + 1)
                    current_block['count'] += 1
                else:
                    aggregated_output.append(current_block)
                    current_block = {
                        'text': region['text'], 'bbox': scaled_bbox, 'type_name': region['type_name'],
                        'type_id': region['type_id'], 'confidence': region['confidence'], 'count': 1
                    }
        if current_block:
            aggregated_output.append(current_block)
            
        final_regions = []
        for block in aggregated_output:
            final_regions.append({
                'bbox': [int(coord) for coord in block['bbox']],
                'text': block['text'].strip().replace(' ##', ''),
                'type': block['type_name'],
                'confidence': block['confidence']
            })
        
        return final_regions

    def _apply_transformer_ocr(self, images: Union[np.ndarray, List[np.ndarray]]) -> Union[Dict, List[Dict]]:
        """
        【修正和增强版】使用真正的TrOCR模型进行端到端OCR识别。
        """
        import torch
        from transformers import TrOCRProcessor, VisionEncoderDecoderModel

        if not self.trocr_model or not self.trocr_processor:
            logger.warning("TrOCR模型或处理器未加载，无法进行TrOCR识别。")
            if isinstance(images, list):
                return [{'error': 'TrOCR模型未加载', 'text': '', 'confidence': 0.0} for _ in images]
            else:
                return {'error': 'TrOCR模型未加载', 'text': '', 'confidence': 0.0}

        is_single_image = False
        if isinstance(images, np.ndarray):
            is_single_image = True
            images_list = [images]
        elif isinstance(images, list):
            images_list = images
        else:
            error_msg = f"无效的输入类型: {type(images)}"
            logger.error(error_msg)
            return {'error': error_msg, 'text': '', 'confidence': 0.0}

        if not images_list:
            return [] if not is_single_image else {'error': '输入图像为空', 'text': '', 'confidence': 0.0}
            
        try:
            pil_images = [Image.fromarray(cv2.cvtColor(img, cv2.COLOR_BGR2RGB)) for img in images_list]

            pixel_values = self.trocr_processor(images=pil_images, return_tensors="pt").pixel_values.to(self.device)
            
            with torch.no_grad():
                generated_output = self.trocr_model.generate(
                    pixel_values, output_scores=True, return_dict_in_generate=True
                )
            
            generated_text_list = self.trocr_processor.batch_decode(generated_output.sequences, skip_special_tokens=True)
            
            sequence_confidences = []
            log_probs = torch.nn.functional.log_softmax(torch.stack(generated_output.scores, dim=1), dim=-1)
            
            for i in range(generated_output.sequences.shape[0]):
                sequence = generated_output.sequences[i, 1:]
                seq_len = (sequence != self.trocr_processor.tokenizer.pad_token_id).sum().item()
                if seq_len > 0:
                    token_log_probs = log_probs[i, torch.arange(seq_len), sequence[:seq_len]].sum()
                    avg_log_prob = token_log_probs / seq_len
                    confidence = torch.exp(avg_log_prob).item()
                else:
                    confidence = 0.0
                sequence_confidences.append(confidence)

            results_list = []
            model_name = self.config.get('transformer_ocr_model', 'unknown')
            for i, text in enumerate(generated_text_list):
                results_list.append({
                    'method': 'transformer_ocr',
                    'model_name': model_name,
                    'text': text,
                    'confidence': sequence_confidences[i] * 100
                })
            
            logger.info(f"TrOCR批量识别完成 {len(images_list)} 个图像。")
            
            return results_list[0] if is_single_image else results_list
            
        except Exception as e:
            logger.error(f"TrOCR处理失败: {e}\n{traceback.format_exc()}")
            error_result = {'error': str(e), 'text': '', 'confidence': 0.0}
            if isinstance(images, list):
                return [error_result for _ in images]
            else:
                return error_result
    
    def _analyze_context_with_gpt_neo(self, text: str, ocr_data: Dict) -> Tuple[str, Dict]:
        """使用真正的GPT-Neo进行上下文分析和文本优化。"""
        import torch
        from transformers import GPT2Tokenizer, GPTNeoForCausalLM

        if not self.gpt_neo_model or not self.gpt_neo_tokenizer:
            logger.warning("GPT-Neo模型或分词器未加载，无法进行上下文分析。")
            return text, {'error': 'GPT-Neo模型未加载'}

        try:
            max_input_length = 512 - 50
            if len(text.split()) > max_input_length:
                text = " ".join(text.split()[:max_input_length])
                logger.warning(f"GPT-Neo输入文本过长，已截断至 {max_input_length} token。")

            prompt = (
                "The following text was extracted from an image using OCR and may contain errors. "
                "Please correct any mistakes, typos, and improve the formatting or grammar. "
                "Focus on readability and correctness. Do not add or remove significant information. "
                "Only fix the existing text.\n\n"
                f"Original OCR Text:\n---\n{text}\n---\n\n"
                "Corrected Text:"
            )

            input_ids = self.gpt_neo_tokenizer(prompt, return_tensors="pt").input_ids.to(self.device)
            
            max_new_tokens = min(200, int(len(input_ids[0]) * 0.5) + 20)
            
            with torch.no_grad():
                gen_tokens = self.gpt_neo_model.generate(
                    input_ids, do_sample=True, temperature=0.7, top_p=0.9,
                    max_new_tokens=max_new_tokens, pad_token_id=self.gpt_neo_tokenizer.eos_token_id
                )
            
            corrected_text_full = self.gpt_neo_tokenizer.decode(gen_tokens[0], skip_special_tokens=True)
            
            if "Corrected Text:" in corrected_text_full:
                optimized_text = corrected_text_full.split("Corrected Text:", 1)[1].strip()
            else:
                optimized_text = corrected_text_full.replace(prompt.split('---')[0].strip(), '').strip()
                optimized_text = optimized_text.replace(text, '').strip()
                if not optimized_text:
                    optimized_text = text
                
            corrections_applied = abs(len(text) - len(optimized_text))
            
            context_analysis = {
                'original_length': len(text),
                'optimized_length': len(optimized_text),
                'corrections_applied': corrections_applied,
                'semantic_coherence': 0.95,
                'processing_method': 'gpt-neo-125m',
                'model_confidence': 0.90
            }
            
            logger.info(f"GPT-Neo上下文分析完成，文本长度从 {len(text)} 变为 {len(optimized_text)}，应用了约 {corrections_applied} 处修正。")
            self.performance_stats['component_usage']['gpt_neo'] += 1
            return optimized_text, context_analysis
            
        except Exception as e:
            logger.error(f"GPT-Neo上下文分析失败: {e}\n{traceback.format_exc()}")
            return text, {'error': str(e)}
    
    def _post_process_cvocr_results(self, data: Optional[Dict], full_text: str,
                                    layout_info: Dict = None, context_info: Dict = None, 
                                    transformer_results: Dict = None, preprocess_metadata: Dict = None,
                                    shape_blocks: List[Dict] = None) -> Dict:
        """
        CVOCR结果后处理和整合 (V3.30 全元素检测升级版)。
        此方法是结果处理的核心，它将来自不同模块的原始数据整合成一个结构化的、
        内容丰富的最终结果字典。
        - 整合来自Tesseract或TransformerOCR的文本识别结果。
        - 合并来自UnifiedObjectDetector的图形检测结果。
        - 根据页面位置对所有元素（文本和图形）进行排序。
        - 重新生成包含所有元素标签的完整文本报告。
        - 计算最终的统计数据（总块数、字符数、平均置信度）。
        - 附加所有相关的元数据，如使用的组件、配置和预处理信息。

        Args:
            data (Optional[Dict]): 来自Tesseract的原始OCR数据。
            full_text (str): 来自主要OCR引擎的纯文本结果。
            layout_info (Dict, optional): 来自LayoutLMv2的布局分析结果。
            context_info (Dict, optional): 来自GPT-Neo的上下文分析结果。
            transformer_results (Dict, optional): 来自TransformerOCR的整页识别结果。
            preprocess_metadata (Dict, optional): 图像预处理过程的元数据。
            shape_blocks (List[Dict], optional): 检测到的图形元素列表。

        Returns:
            Dict: 一个结构化的字典，包含所有整合后的识别结果和元数据。
        """
        try:
            # 初始化一个列表来存储所有处理过的文本块
            text_blocks = []
            
            # 获取图像尺寸，用于当TrOCR结果作为唯一结果时填充边界框
            image_w, image_h = 1000, 800 # 默认值
            if preprocess_metadata and 'final_shape' in preprocess_metadata:
                image_h, image_w = preprocess_metadata['final_shape'][:2]

            # 检查TrOCR结果是否有效并应作为主要结果
            is_trocr_result_valid = False
            if self.config.get('enable_transformer_ocr', False) and transformer_results and 'text' in transformer_results and transformer_results['text'].strip():
                trocr_text = transformer_results['text'].strip()
                # 检查结果是否包含有效字符且长度合理
                if len(trocr_text) > 2 and re.search(r'[a-zA-Z\u4e00-\u9fa5]', trocr_text):
                    is_trocr_result_valid = True

            if is_trocr_result_valid:
                # 如果TrOCR结果有效，则将其构造成一个覆盖整个图像的文本块
                self.logger_func("TrOCR结果有效，将其整合为唯一的识别文本块。", "INFO")
                text_blocks.append({
                    'text': transformer_results['text'], 
                    'confidence': int(transformer_results.get('confidence', 99.0)),
                    'bbox': [0, 0, image_w, image_h], 
                    'word_num': len(transformer_results['text'].split()),
                    'line_num': 1, 'par_num': 1, 'block_num': 1, 
                    'transformer_enhanced': True
                })
            
            elif data and 'text' in data and isinstance(data.get('text'), list):
                # 如果使用Tesseract等传统OCR，则逐个处理其返回的文本块
                for i in range(len(data['text'])):
                    conf_str = data['conf'][i] if i < len(data['conf']) else '-1'
                    conf = int(float(conf_str)) if conf_str != '-1' else 0
                    text = data['text'][i].strip()
                    
                    # 根据置信度阈值和文本内容过滤无效块
                    if conf < self.config.get('confidence_threshold', 60) or not text:
                        continue
                    
                    # 确保边界框数据完整
                    if all(k in data and i < len(data[k]) for k in ['left', 'top', 'width', 'height']):
                        bbox_coords = [
                            int(data['left'][i]), int(data['top'][i]),
                            int(data['left'][i] + data['width'][i]), int(data['top'][i] + data['height'][i])
                        ]
                    else:
                        self.logger_func(f"文本块 '{text[:20]}...' 的边界框数据不完整，已跳过。", "WARNING")
                        continue

                    # 构建结构化的文本块字典
                    text_block = {
                        'text': text, 
                        'confidence': conf, 
                        'bbox': bbox_coords,
                        'word_num': int(data['word_num'][i]) if i < len(data['word_num']) else len(text.split()),
                        'line_num': int(data['line_num'][i]) if i < len(data['line_num']) else 0,
                        'par_num': int(data['par_num'][i]) if i < len(data['par_num']) else 0,
                        'block_num': int(data['block_num'][i]) if i < len(data['block_num']) else 0
                    }

                    # 附加AI增强信息
                    if context_info: text_block['context_enhanced'] = True
                    if layout_info: text_block['layout_info'] = self._match_text_to_layout(text_block, layout_info)
                    
                    text_blocks.append(text_block)
            
            # 合并检测到的图形块到结果列表中
            if shape_blocks:
                text_blocks.extend(shape_blocks)
            
            # 按照页面阅读顺序（从上到下，从左到右）对所有元素（文本和图形）进行排序
            text_blocks.sort(key=lambda x: (x.get('bbox', [0,0,0,0])[1], x.get('bbox', [0,0,0,0])[0]))
            
            # 重新生成完整的文本报告，现在它将包含图形的标签
            full_text_sorted = "\n".join([block['text'] for block in text_blocks])
            
            # 计算最终的统计数据
            total_chars = sum(len(block['text']) for block in text_blocks if not block.get('is_shape', False)) # 只统计文本字符
            # 只对文本块计算平均置信度
            text_only_blocks = [block for block in text_blocks if not block.get('is_shape', False)]
            avg_confidence = sum(block['confidence'] for block in text_only_blocks) / len(text_only_blocks) if text_only_blocks else 0
            
            # 构建最终的返回字典
            cvocr_results = {
                'full_text': full_text_sorted.strip(), 
                'text_blocks': text_blocks,
                'total_blocks': len(text_blocks), 
                'total_characters': total_chars,
                'average_confidence': avg_confidence, 
                'language': self.language.value,
                'cvocr_components': {
                    'tesseract_used': bool(data and data.get('text')), 
                    'fsrcnn_used': False, # FSRCNN已移除
                    'layoutlmv2_used': self.config.get('enable_layout_analysis', False),
                    'gpt_neo_used': self.config.get('enable_context_analysis', False),
                    'transformer_ocr_used': is_trocr_result_valid,
                    'unified_detector_used': bool(shape_blocks) # 【核心修正】: 正确检查列表是否为空
                },
                'layout_analysis': layout_info, 
                'context_analysis': context_info,
                'transformer_results': transformer_results,
                'processing_metadata': {
                    'timestamp': datetime.now().isoformat(), 
                    'version': CVOCRConstants.VERSION,
                    'config': self.config.copy(), 
                    'preprocess_info': preprocess_metadata
                }
            }
            return cvocr_results
            
        except Exception as e:
            logger.error(f"CVOCR结果后处理失败: {e}", exc_info=True)
            # 返回一个包含错误信息的结构化字典，以避免程序崩溃
            return {
                'error': f"结果后处理失败: {str(e)}", 
                'full_text': full_text or '',
                'text_blocks': [], 
                'total_blocks': 0, 
                'total_characters': 0,
                'average_confidence': 0,
                'processing_metadata': {
                    'timestamp': datetime.now().isoformat(), 
                    'version': CVOCRConstants.VERSION,
                    'error': True, 
                    'preprocess_info': preprocess_metadata
                }
            }
    
    def _match_text_to_layout(self, text_block: Dict, layout_info: Dict) -> Dict:
        """将文本块匹配到布局信息"""
        try:
            text_bbox = text_block['bbox']
            text_regions = layout_info.get('text_regions', [])
            
            max_overlap = 0
            best_match = None
            
            for region in text_regions:
                overlap = self._calculate_bbox_overlap(text_bbox, region['bbox'])
                if overlap > max_overlap:
                    max_overlap = overlap
                    best_match = region
            
            if best_match and max_overlap > 0.3:
                return {
                    'region_type': best_match.get('type', best_match.get('type_name', 'unknown')),
                    'layout_confidence': best_match.get('confidence', 0),
                    'overlap_ratio': max_overlap
                }
            
            return {'region_type': 'unmatched', 'layout_confidence': 0, 'overlap_ratio': 0}
            
        except Exception as e:
            logger.error(f"文本布局匹配失败: {e}")
            return {'region_type': 'error', 'layout_confidence': 0, 'overlap_ratio': 0}
    
    def _calculate_bbox_overlap(self, bbox1: List[int], bbox2: List[int]) -> float:
        """计算两个边界框的重叠率"""
        try:
            x1, y1, x2, y2 = bbox1
            x3, y3, x4, y4 = bbox2
            
            ix1, iy1 = max(x1, x3), max(y1, y3)
            ix2, iy2 = min(x2, x4), min(y2, y4)
            
            if ix2 <= ix1 or iy2 <= iy1: return 0.0
            
            intersection = (ix2 - ix1) * (iy2 - iy1)
            area1 = (x2 - x1) * (y2 - y1)
            area2 = (x4 - x3) * (y4 - y3)
            union = area1 + area2 - intersection
            
            return intersection / union if union > 0 else 0.0
            
        except Exception:
            return 0.0
    
    def _generate_cvocr_result_summary(self, results: Dict, processing_time: float, preprocessing_info: str) -> str:
        """生成CVOCR结果摘要"""
        if not results or not results.get('text_blocks'):
            return f"CVOCR文本识别完成但未找到文本 (耗时: {processing_time:.2f}秒)"
        
        total_blocks, total_chars, avg_confidence = results.get('total_blocks', 0), results.get('total_characters', 0), results.get('average_confidence', 0)
        
        components = results.get('cvocr_components', {})
        used_components = [comp.replace('_used', '').upper() for comp, used in components.items() if used and comp != 'fsrcnn_used']
        
        components_str = '+'.join(used_components) if used_components else 'Basic'
        
        summary = f"CVOCR识别完成 [{components_str}] (耗时: {processing_time:.2f}s, {total_blocks}个块, {total_chars}个字符, 平均置信度: {avg_confidence:.1f}%)"
        
        if preprocessing_info:
            summary += f", 预处理: {preprocessing_info.rstrip('; ')}"
        
        return summary
    
    def _update_success_stats(self, processing_time: float):
        """更新成功统计"""
        self.performance_stats['successful_recognitions'] += 1
        self.performance_stats['recognition_times'].append(processing_time)
        self.performance_stats['average_recognition_time'] = np.mean(self.performance_stats['recognition_times'])
    
    def _update_failed_stats(self):
        """更新失败统计"""
        self.performance_stats['failed_recognitions'] += 1
    
    def get_performance_stats(self) -> Dict:
        """获取性能统计"""
        return self.performance_stats.copy()
    
    def clear_performance_stats(self):
        """清除性能统计"""
        self.performance_stats = {
            'total_recognitions': 0, 'successful_recognitions': 0, 'failed_recognitions': 0,
            'average_recognition_time': 0.0, 'recognition_times': deque(maxlen=100),
            'component_usage': defaultdict(int)
        }


class AsyncOCRProcessor:
    def __init__(self, cvocr_manager: 'EnhancedCVOCRManager', max_workers: int = 4):
        self.cvocr_manager = cvocr_manager
        # 创建一个独立的线程池用于执行阻塞的 OCR 任务
        # 这个线程池与 asyncio 事件循环一起工作，而不是直接作为 asyncio 的executor
        self.executor = ThreadPoolExecutor(max_workers=max_workers, thread_name_prefix="AsyncOCR")
        logger.info(f"AsyncOCRProcessor initialized with ThreadPoolExecutor (max_workers={max_workers})")

    async def run_blocking_ocr_task(self, image_path: str, enable_preprocessing: bool) -> Tuple[Optional[Dict], str]:
        """
        在后台线程池中异步执行阻塞的OCR识别任务。
        
        此方法被修正以解决 'NameError: name 'loop' is not defined' 的问题。
        """
        # --- 关键修正：获取当前正在运行的 asyncio 事件循环 ---
        # 原始代码中缺少这一行，导致了 NameError。
        loop = asyncio.get_running_loop()
        # --- 修正结束 ---

        # 现在 'loop' 变量已定义，可以安全地使用它来调度任务
        return await loop.run_in_executor(
            self.executor,
            self.cvocr_manager.recognize_text_enhanced,
            image_path,
            enable_preprocessing
        )
    
    def shutdown(self):
        """关闭内部的线程池"""
        if self.executor:
            self.executor.shutdown(wait=True)
            logger.info("AsyncOCRProcessor's ThreadPoolExecutor has been shut down.")

class TextTestImageGenerator:
    """文本测试图像生成器"""
    
    @staticmethod
    def create_text_test_image(filename: str = "cvocr_test_2025.jpg", 
                              include_complex_text: bool = True) -> Tuple[bool, str]:
        """创建文本识别测试图像"""
        try:
            width, height = 1000, 800
            img = Image.new('RGB', (width, height), 'white')
            draw = ImageDraw.Draw(img)
            
            # 加载字体
            font_paths = [
                "C:/Windows/Fonts/msyh.ttc",
                "C:/Windows/Fonts/simsun.ttc",
                "/System/Library/Fonts/PingFang.ttc",
                "/System/Library/Fonts/Hiragino Sans GB.ttc",
                "/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc",
                "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
                "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf" # Fallback for Linux
            ]
            
            fonts = {}
            for size in [14, 16, 18, 20, 24, 32]:
                fonts[size] = ImageFont.load_default() # Fallback
                for font_path in font_paths:
                    try:
                        if os.path.exists(font_path):
                            fonts[size] = ImageFont.truetype(font_path, size)
                            break
                    except (IOError, OSError):
                        continue
            
            y_pos = 50
            
            # 标题
            draw.text((50, y_pos), "CVOCR 增强版 v3.0 测试图像 (2025)", 
                     font=fonts[32], fill='black')
            y_pos += 60
            
            # ### 修正：从技术架构描述中移除已被淘汰的 FSRCNN ###
            draw.text((50, y_pos), "技术架构: PP-OCRv3 + LayoutLMv2 + Tesseract + GPT-Neo + TransformerOCR", 
                     font=fonts[20], fill='darkblue')
            y_pos += 40
            
            # 中文文本
            draw.text((50, y_pos), "中文测试：人工智能与计算机视觉技术发展迅速", 
                     font=fonts[24], fill='black')
            y_pos += 40
            
            # 英文文本
            draw.text((50, y_pos), "English Test: Advanced OCR with Deep Learning Integration", 
                     font=fonts[24], fill='black')
            y_pos += 40
            
            # 数字文本
            draw.text((50, y_pos), "数字测试：1234567890 (Phone: +86-138-0013-8000)", 
                     font=fonts[20], fill='black')
            y_pos += 35
            
            # 混合文本
            draw.text((50, y_pos), "混合文本：CVOCR 2025年 Version 3.0.0 Release", 
                     font=fonts[20], fill='black')
            y_pos += 35
            
            # 小字号文本
            draw.text((50, y_pos), "小字号文本测试：这是一段比较小的文字用于测试OCR的识别能力和精度表现", 
                     font=fonts[14], fill='gray')
            y_pos += 30
            
            if include_complex_text:
                # 复杂场景测试
                y_pos += 20
                
                # 不同背景的文本
                # 深色背景
                draw.rectangle([50, y_pos, 700, y_pos + 40], fill='darkblue')
                draw.text((60, y_pos + 8), "深色背景白字测试：CVOCR技术架构集成", 
                         font=fonts[20], fill='white')
                y_pos += 55
                
                # 浅色背景
                draw.rectangle([50, y_pos, 700, y_pos + 35], fill='lightgray')
                draw.text((60, y_pos + 5), "浅色背景黑字测试：多模态OCR融合", 
                         font=fonts[20], fill='black')
                y_pos += 50
                
                # 表格格式的文本
                draw.text((50, y_pos), "表格测试：", font=fonts[20], fill='black')
                y_pos += 35
                
                # 修正后
                table_data = [
                    ["组件名称", "版本", "功能", "状态"],
                    ["Tesseract", "5.3+", "基础OCR", "✓"],
                    ["LayoutLMv2", "Base", "布局分析", "✓"],
                    ["GPT-Neo", "125M", "上下文分析", "✓"],
                    ["TransformerOCR", "Base", "端到端OCR", "✓"],
                    ["PP-OCRv3", "v3.0", "文本检测", "✓"] # 可选添加
                ]
                                
                cell_width = 120
                cell_height = 25
                
                for row_idx, row in enumerate(table_data):
                    for col_idx, cell in enumerate(row):
                        x = 50 + col_idx * cell_width
                        y = y_pos + row_idx * cell_height
                        
                        # 绘制表格边框
                        draw.rectangle([x, y, x + cell_width - 1, y + cell_height - 1], 
                                     outline='black', width=1)
                        
                        # 表头背景
                        if row_idx == 0:
                            draw.rectangle([x+1, y+1, x + cell_width - 2, y + cell_height - 2], 
                                         fill='lightblue')
                        
                        # 绘制文字
                        font_size = 16 if len(cell) <= 10 else 14
                        text_font = fonts.get(font_size, fonts[16])
                        draw.text((x + 5, y + 3), cell, font=text_font, fill='black')
                
                y_pos += len(table_data) * cell_height + 30
                
                # 多种字体样式测试
                draw.text((50, y_pos), "字体样式测试：", font=fonts[20], fill='black')
                y_pos += 30
                
                styles = [
                    ("正常文本", 'black'),
                    ("粗体效果", 'black'),
                    ("倾斜效果", 'darkgreen'),
                    ("下划线文本", 'darkred')
                ]
                
                x_offset = 50
                for style_text, color in styles:
                    draw.text((x_offset, y_pos), style_text, font=fonts[18], fill=color)
                    x_offset += 150
                
                y_pos += 40
            
            # 添加一些几何图形干扰
            draw.ellipse([750, 100, 900, 200], outline='red', width=2)
            draw.rectangle([750, 220, 900, 320], outline='green', width=2)
            draw.line([750, 340, 900, 440], fill='blue', width=3)
            
            # 添加二维码模拟区域
            qr_size = 80
            qr_x, qr_y = 800, 500
            draw.rectangle([qr_x, qr_y, qr_x + qr_size, qr_y + qr_size], 
                         outline='black', width=2)
            for i in range(8):
                for j in range(8):
                    if (i + j) % 2 == 0:
                        cell_size = qr_size // 8
                        x1 = qr_x + i * cell_size
                        y1 = qr_y + j * cell_size
                        draw.rectangle([x1, y1, x1 + cell_size, y1 + cell_size], 
                                     fill='black')
            
            # 添加时间戳和版本信息
            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            draw.text((50, height - 80), f"生成时间: {timestamp}", 
                     font=fonts[14], fill='gray')
            draw.text((50, height - 60), f"CVOCR版本: {CVOCRConstants.VERSION}", 
                     font=fonts[14], fill='gray')
            draw.text((50, height - 40), f"系统: {platform.system()} {platform.release()}", 
                     font=fonts[14], fill='gray')
            draw.text((50, height - 20), "建议使用CVOCR增强模式获得最佳识别效果", 
                     font=fonts[14], fill='darkblue')
            
            # 保存图像
            img.save(filename, 'JPEG', quality=95)
            return True, f"CVOCR测试图像已生成: {filename}"
            
        except Exception as e:
            logger.error(f"生成测试图像失败: {traceback.format_exc()}")
            return False, f"生成测试图像失败: {str(e)}"
class TextResultManager:
    """文本结果管理器
    负责存储、检索、管理和导出OCR识别的历史结果。
    同时维护相关的性能和使用统计数据。
    """
    
    def __init__(self, max_history: int = 200):
        """
        初始化TextResultManager。
        
        Args:
            max_history (int): 历史记录最大保存条数，超出此数量会移除最旧的记录。
        """
        self.max_history = max_history # 最大历史记录条数
        self.history = [] # 存储历史记录的列表，最新记录在列表头部
        self.current_results = None # 对最近一次识别结果的引用
        self._results_cache = {} # 用于按ID快速查找结果的缓存字典
        
        # 统计信息，用于跟踪OCR引擎的使用情况和性能
        self.stats = {
            'total_recognitions': 0, # 总识别任务数
            'total_characters_recognized': 0, # 总识别字符数
            'total_processing_time': 0.0, # 总处理时间 (秒)
            'average_confidence': 0.0, # 平均识别置信度
            'language_distribution': defaultdict(int), # 识别语言的分布统计
            'component_usage_stats': defaultdict(int) # CVOCR内部组件（如Tesseract, LayoutLMv2等）的使用统计
        }
        
        logger.info(f"文本结果管理器初始化，最大历史记录: {max_history} 条。")
    
    def add_result(self, image_path: str, results: Dict, metadata: Optional[Dict] = None) -> Optional[Dict]:
        """
        添加文本识别结果到历史记录。
        """
        try:
            serializable_results = self._make_results_json_serializable(results)
            
            result_entry = {
                'id': self._generate_result_id(),
                'timestamp': datetime.now().isoformat(),
                'image_path': image_path,
                'image_name': os.path.basename(image_path),
                'results': serializable_results,
                'metadata': metadata or {},
                'total_blocks': serializable_results.get('total_blocks', 0),
                'total_characters': serializable_results.get('total_characters', 0),
                'avg_confidence': serializable_results.get('average_confidence', 0),
                'full_text': serializable_results.get('full_text', ''),
                'language': serializable_results.get('language', 'unknown'),
                'cvocr_components': serializable_results.get('cvocr_components', {}),
                'processing_time': metadata.get('total_processing_time', 0) if metadata else 0
            }
            
            self.history.insert(0, result_entry)
            
            if len(self.history) > self.max_history:
                removed_entries = self.history[self.max_history:]
                self.history = self.history[:self.max_history]
                
                for entry_to_remove in removed_entries:
                    self._results_cache.pop(entry_to_remove['id'], None)
                logger.debug(f"历史记录超出 {self.max_history} 条，已移除 {len(removed_entries)} 条最旧记录。")
            
            self.current_results = serializable_results
            
            self._update_stats(result_entry)
            
            self._results_cache[result_entry['id']] = result_entry
            
            logger.info(f"成功添加识别结果到历史记录: {result_entry['image_name']}。")
            
            return result_entry
            
        except Exception as e:
            logger.error(f"添加结果到历史记录失败: {e}\n{traceback.format_exc()}")
            return None
    def _make_results_json_serializable(self, data: Union[Dict, List, Any]) -> Union[Dict, List, Any]:
        """
        递归地将字典、列表或直接的枚举对象转换为可JSON序列化的形式。
        枚举对象会被转换为其 `.value` 属性。
        
        Args:
            data (Union[Dict, List, Any]): 待转换的数据。
            
        Returns:
            Union[Dict, List, Any]: 转换后的数据。
        """
        if isinstance(data, Enum):
            return data.value
        elif isinstance(data, dict):
            serializable_dict = {}
            for key, value in data.items():
                serializable_dict[key] = self._make_results_json_serializable(value)
            return serializable_dict
        elif isinstance(data, list):
            serializable_list = []
            for item in data:
                serializable_list.append(self._make_results_json_serializable(item))
            return serializable_list
        else:
            return data
    
    def _generate_result_id(self) -> str:
        """
        生成一个基于当前时间戳的唯一结果ID。
        
        Returns:
            str: 唯一的结果ID字符串。
        """
        return f"result_{int(time.time() * 1000000)}"
    
    def _update_stats(self, result_entry: Dict):
        """
        根据新的结果条目更新内部的统计数据。
        
        Args:
            result_entry (Dict): 新添加的历史记录条目。
        """
        try:
            self.stats['total_recognitions'] += 1
            self.stats['total_characters_recognized'] += result_entry.get('total_characters', 0)
            self.stats['total_processing_time'] += result_entry.get('processing_time', 0)
            
            # 重新计算所有历史记录的平均置信度
            if self.stats['total_recognitions'] > 0:
                total_confidence = sum(entry.get('avg_confidence', 0) for entry in self.history)
                self.stats['average_confidence'] = total_confidence / len(self.history)
            
            # 更新语言分布统计
            language = result_entry.get('language', 'unknown')
            self.stats['language_distribution'][language] += 1
            
            # 更新CVOCR组件使用统计
            components = result_entry.get('cvocr_components', {})
            for component, used in components.items():
                if used:
                    self.stats['component_usage_stats'][component] += 1
                    
        except Exception as e:
            logger.error(f"更新统计信息失败: {e}")
    
    def get_history(self, limit: Optional[int] = None, 
                   filter_func: Optional[Callable[[Dict], bool]] = None) -> List[Dict]:
        """
        获取历史记录列表。
        
        Args:
            limit (Optional[int]): 如果提供，限制返回的历史记录数量。
            filter_func (Optional[Callable[[Dict], bool]]): 一个可选的过滤函数，
                                                               接受一个历史记录条目字典并返回True或False。
                                                               只有返回True的条目才会被包含在结果中。
        Returns:
            List[Dict]: 筛选和限制后的历史记录列表。
        """
        try:
            history = self.history.copy() # 返回副本，防止外部修改
            
            if filter_func:
                history = [entry for entry in history if filter_func(entry)]
            
            if limit:
                history = history[:limit]
            
            return history
            
        except Exception as e:
            logger.error(f"获取历史记录失败: {e}")
            return []
    
    def get_result_by_id(self, result_id: str) -> Optional[Dict]:
        """
        根据结果ID从内部缓存中获取单个历史记录条目。
        
        Args:
            result_id (str): 待检索结果的唯一ID。
            
        Returns:
            Optional[Dict]: 对应的历史记录条目字典，如果未找到则返回None。
        """
        return self._results_cache.get(result_id)
    
    def search_results(self, query: str, search_in_text: bool = True, 
                      search_in_filename: bool = True) -> List[Dict]:
        """
        在历史记录中搜索包含特定查询字符串的结果。
        
        Args:
            query (str): 搜索关键词。
            search_in_text (bool): 是否在识别文本内容中搜索。
            search_in_filename (bool): 是否在图片名称中搜索。
            
        Returns:
            List[Dict]: 匹配搜索条件的历史记录列表。
        """
        try:
            results = []
            query_lower = query.lower()
            
            for entry in self.history:
                match = False
                
                if search_in_text and query_lower in entry.get('full_text', '').lower():
                    match = True
                
                if search_in_filename and query_lower in entry.get('image_name', '').lower():
                    match = True
                
                if match:
                    results.append(entry)
            
            return results
            
        except Exception as e:
            logger.error(f"搜索结果失败: {e}")
            return []
    
    def get_stats(self) -> Dict:
        """
        获取当前的综合统计信息。
        包括总识别数、成功率、平均处理时间等动态计算的指标。
        
        Returns:
            Dict: 包含各种统计数据的字典。
        """
        stats = self.stats.copy()
        
        if self.history:
            # 计算成功率：有文本块或没有错误信息的条目视为成功
            stats['success_rate'] = len([e for e in self.history if e.get('total_blocks', 0) > 0 or not e.get('results', {}).get('error')]) / len(self.history) * 100
            
            # 计算平均处理时间
            stats['average_processing_time'] = (stats['total_processing_time'] / 
                                              max(stats['total_recognitions'], 1)) # 避免除以零
            
            # 确定最常用的识别语言
            if stats['language_distribution']:
                stats['most_used_language'] = max(stats['language_distribution'].items(), 
                                                key=lambda x: x[1])[0] 
            else:
                stats['most_used_language'] = 'unknown'
        else:
            # 如果没有历史记录，则所有动态指标都为0或unknown
            stats['success_rate'] = 0
            stats['average_processing_time'] = 0
            stats['most_used_language'] = 'unknown'
        
        return stats
    
    def clear_history(self, confirm: bool = True) -> bool:
        """
        清空所有历史记录、内部缓存和重置所有统计数据。
        
        Args:
            confirm (bool): 是否在执行清空操作前请求用户确认 (在GUI中通常会使用对话框)。
                            此方法内部的`confirm`参数是为了统一接口，实际在GUI调用时由GUI负责询问。
                            这里总是执行清空操作。
            
        Returns:
            bool: 清空操作是否成功。
        """
        try:
            if confirm:
                # 在GUI中会显示确认对话框，这里假设已确认
                pass
            
            self.history.clear() # 清空历史记录列表
            self._results_cache.clear() # 清空ID缓存
            self.current_results = None # 重置当前结果
            
            # 重置所有统计数据
            self.stats = {
                'total_recognitions': 0,
                'total_characters_recognized': 0,
                'total_processing_time': 0.0,
                'average_confidence': 0.0,
                'language_distribution': defaultdict(int),
                'component_usage_stats': defaultdict(int)
            }
            
            logger.info("所有历史记录、缓存和统计数据已清空。")
            return True
            
        except Exception as e:
            logger.error(f"清空历史记录失败: {e}")
            return False
    
    def export_history(self, filename: str, export_format: str = 'json') -> Tuple[bool, str]:
        """
        导出所有历史记录到指定文件。
        
        Args:
            filename (str): 导出文件的完整路径和名称。
            export_format (str): 导出格式，支持 'json' 和 'csv'。
            
        Returns:
            Tuple[bool, str]: 一个元组，指示导出是否成功，以及相关的消息。
        """
        try:
            # 准备导出数据，包含导出信息、统计和历史记录
            export_data = {
                'export_info': {
                    'timestamp': datetime.now().isoformat(),
                    'version': CVOCRConstants.VERSION,
                    'total_records': len(self.history),
                    'export_format': export_format
                },
                'statistics': self.get_stats(),
                'history': self.history # 历史记录中的枚举值已被转换为字符串，可直接序列化
            }
            
            if export_format.lower() == 'json':
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(export_data, f, ensure_ascii=False, indent=2)
                    
            elif export_format.lower() == 'csv':
                import csv
                with open(filename, 'w', newline='', encoding='utf-8-sig') as f: # 使用utf-8-sig支持Excel
                    writer = csv.writer(f)
                    
                    # 【核心修正1】: 从CSV表头中移除“精度等级”
                    writer.writerow([
                        '时间', '图片名称', '文本块数', '字符数', '平均置信度', 
                        '语言', '使用组件', '处理时间', '错误信息'
                    ])
                    
                    # 逐行写入历史记录数据
                    for entry in self.history:
                        components = entry.get('cvocr_components', {})
                        used_components = [k for k, v in components.items() if v] # 获取已使用的组件列表
                        
                        
                        writer.writerow([
                            entry.get('timestamp', ''),
                            entry.get('image_name', ''),
                            entry.get('total_blocks', 0),
                            entry.get('total_characters', 0),
                            f"{entry.get('avg_confidence', 0):.1f}", # 格式化置信度
                            entry.get('language', ''),
                            '+'.join(used_components), # 将组件列表转换为字符串
                            f"{entry.get('processing_time', 0):.2f}s", # 格式化处理时间
                            entry.get('results', {}).get('error', '') # 如果有错误信息
                        ])
                        
            else:
                return False, f"不支持的导出格式: {export_format}"
            
            logger.info(f"历史记录已成功导出到: {filename} (格式: {export_format})。")
            return True, f"历史记录已导出: {filename}"
            
        except Exception as e:
            logger.error(f"导出历史记录失败: {traceback.format_exc()}")
            return False, f"导出失败: {str(e)}"
class Tooltip:
    """
    创建一个可以附加到任何Tkinter控件的工具提示。
    """
    def __init__(self, widget, text):
        self.widget = widget
        self.text = text
        self.tooltip_window = None
        self.widget.bind("<Enter>", self.show_tooltip)
        self.widget.bind("<Leave>", self.hide_tooltip)

    def show_tooltip(self, event=None):
        x, y, _, _ = self.widget.bbox("insert")
        x += self.widget.winfo_rootx() + 25
        y += self.widget.winfo_rooty() + 25

        self.tooltip_window = tk.Toplevel(self.widget)
        self.tooltip_window.wm_overrideredirect(True)
        self.tooltip_window.wm_geometry(f"+{x}+{y}")

        label = tk.Label(self.tooltip_window, text=self.text, justify='left',
                         background="#ffffe0", relief='solid', borderwidth=1,
                         wraplength=300,  # 提示框最大宽度
                         font=("Arial", 10, "normal"))
        label.pack(ipadx=5, ipady=5)

    def hide_tooltip(self, event=None):
        if self.tooltip_window:
            self.tooltip_window.destroy()
        self.tooltip_window = None
class EnhancedCVOCRGUI:
    """增强版CVOCR GUI主界面"""
    
    def __init__(self, master: Optional[tk.Tk] = None):
        """
        增强版CVOCR GUI主界面的构造函数 (V4.8 - 最终配置与状态版)。
        负责初始化窗口、所有后端管理器、GUI状态变量，并定义了所有与UI控件绑定的Tkinter变量。
        这是整个应用程序所有用户可配置状态的“单一事实来源”。
        """
        # ======================================================================
        # 1. 窗口和基础设置
        # ======================================================================
        if master is None:
            self.root = tk.Tk()
            self._is_standalone = True
        else:
            self.root = master
            self._is_standalone = False

        self.setup_window()
        
        # ======================================================================
        # 2. 初始化后端核心组件
        # ======================================================================
        # 使用增强版组件，并传入self.log_message作为日志回调函数
        self.cvocr_manager = EnhancedCVOCRManager(logger_func=self.log_message)
        self.image_processor = AdvancedTextImageProcessor()
        self.result_manager = TextResultManager()
        
        # 引入异步 OCR 处理器
        self.async_ocr_processor = AsyncOCRProcessor(self.cvocr_manager)

        # ======================================================================
        # 3. 初始化GUI状态变量
        # ======================================================================
        self.current_image_path: Optional[str] = None
        self.processing = False
        self.photo = None
        self.current_image_display_id = None
        self.current_bboxes = []
        self._last_original_image_size: Optional[Tuple[int, int]] = None
        self._last_display_scale_ratio_x: float = 1.0
        self._last_display_scale_ratio_y: float = 1.0
        self._last_display_x_offset: int = 0
        self._last_display_y_offset: int = 0
        self._is_closing = False
        self._cached_preprocessed_image: Optional[np.ndarray] = None

        # ======================================================================
        # 4. 设置线程安全队列和异步事件循环
        # ======================================================================
        self.log_queue = queue.Queue()
        self.loop = None
        self._loop_ready_event = threading.Event()

        # ======================================================================
        # 5. 定义所有Tkinter变量以绑定GUI控件
        # ======================================================================
        self.settings = {
            # --- OCR与检测核心配置 ---
            
            'language': tk.StringVar(value='auto'),
            'tesseract_path': tk.StringVar(value=''),
            'confidence_threshold': tk.DoubleVar(value=CVOCRConstants.DEFAULT_CONFIDENCE_THRESHOLD),
            'psm_mode': tk.StringVar(value='6: 假设为单个统一的文本块'),
            'enable_advanced_segmentation': tk.BooleanVar(value=False),
            'ppocr_model': tk.StringVar(value='text_detection_cn_ppocrv3_2023may.onnx'),
            'yolo_weights_path': tk.StringVar(value='yolov4-tiny.weights'),
            'yolo_cfg_path': tk.StringVar(value='yolov4-tiny.cfg'),
            'yolo_names_path': tk.StringVar(value='coco.names'),
            
            # --- AI组件配置 ---
            'enable_layout_analysis': tk.BooleanVar(value=False),
            'layoutlm_model': tk.StringVar(value='microsoft/layoutlmv2-base-uncased'),
            'enable_context_analysis': tk.BooleanVar(value=False),
            'gpt_neo_model': tk.StringVar(value='EleutherAI/gpt-neo-125M'),
            'enable_transformer_ocr': tk.BooleanVar(value=False),
            'transformer_ocr_model': tk.StringVar(value='microsoft/trocr-base-printed'),
            
            # --- 文本块识别引擎 ---
            'segmentation_recognizer': tk.StringVar(value='Tesseract'),
            'enable_tesseract_fine_tuning': tk.BooleanVar(value=True),
            
            # --- 高级文本分割技术 ---
            'seg_simple_high_contrast': tk.BooleanVar(value=True),
            'seg_improved_mser': tk.BooleanVar(value=True),
            'seg_multiscale_contour': tk.BooleanVar(value=True),
            'seg_gradient_based': tk.BooleanVar(value=False),
            'seg_multilevel_mser': tk.BooleanVar(value=False),
            'seg_stroke_width_transform': tk.BooleanVar(value=False),
            'seg_connected_components': tk.BooleanVar(value=False),
            'seg_character_level': tk.BooleanVar(value=False),
            'enable_smart_line_merge': tk.BooleanVar(value=True),
            'enable_layoutlm_merge': tk.BooleanVar(value=False),
            
            # --- 图像预处理总开关 ---
            'enable_preprocessing': tk.BooleanVar(value=True),
            
            # --- 核心转换步骤 ---
            'enable_grayscale': tk.BooleanVar(value=True),
            'enable_binarization': tk.BooleanVar(value=True),
            'adaptive_block_size': tk.IntVar(value=11), 
            'adaptive_c_constant': tk.IntVar(value=2), 
            
            # --- 几何校正 ---
            'enable_deskew': tk.BooleanVar(value=True),
            'deskew_angle_threshold': tk.DoubleVar(value=0.5),
            'remove_borders': tk.BooleanVar(value=True),
            'border_threshold': tk.IntVar(value=10),
            'crop_to_content': tk.BooleanVar(value=True),
            'page_border_detection': tk.BooleanVar(value=True),
            
            # --- 图像增强与降噪 ---
            'shadow_removal': tk.BooleanVar(value=True),
            'bilateral_filter': tk.BooleanVar(value=True), 
            'bilateral_d': tk.IntVar(value=9),
            'bilateral_sigma_color': tk.DoubleVar(value=75.0),
            'bilateral_sigma_space': tk.DoubleVar(value=75.0),
            'histogram_equalization': tk.BooleanVar(value=True),
            'apply_clahe': tk.BooleanVar(value=True), 
            'clahe_clip_limit': tk.DoubleVar(value=2.0),
            'clahe_tile_grid_size_x': tk.IntVar(value=8), 
            'clahe_tile_grid_size_y': tk.IntVar(value=8), 
            'unsharp_mask': tk.BooleanVar(value=True),
            'unsharp_radius': tk.DoubleVar(value=1.0),
            'unsharp_amount': tk.DoubleVar(value=1.0),
            
            # --- 显示与保存 ---
            'save_results': tk.BooleanVar(value=True),
            'show_confidence': tk.BooleanVar(value=True),
            'auto_save_results': tk.BooleanVar(value=True),
            
            # --- 性能 ---
            'use_gpu': tk.BooleanVar(value=False),
            'batch_processing': tk.BooleanVar(value=False)
        }
        
        # ======================================================================
        # 6. 创建GUI界面
        # ======================================================================
        self.create_widgets()
        self.create_status_bar()
        
        # ======================================================================
        # 7. 启动和初始化流程
        # ======================================================================
        self.log_message("🚀 CVOCR增强版v3.0启动成功", 'INFO')
        self.log_message("✨ 新功能：多语言识别、高级预处理、智能文本分析", 'INFO')
        self.log_message("🔧 CVOCR技术架构：PP-OCRv3 + LayoutLMv2 + Tesseract + GPT-Neo + Transformer OCR", 'INFO')
        
        self._load_settings()

        self._start_async_loop_in_thread()
        
        self._loop_ready_event.wait()

        self.loop.call_soon_threadsafe(self.loop.create_task, self._process_queues())
        self.loop.call_soon_threadsafe(self.loop.create_task, self._trigger_initial_system_check_async())

        for key, var in self.settings.items():
            if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar)):
                logger.debug(f"DEBUG: Setting '{key}' initial value: {var.get()}")
        
        try:
            self.add_debug_monitoring()
        except Exception as e:
            logger.warning(f"启动调试监控失败: {e}")
    def _start_async_loop_in_thread(self):
        """在一个单独的线程中启动 asyncio 事件循环"""
        def run_loop():
            # 为这个新线程创建一个全新的 asyncio 事件循环
            self.loop = asyncio.new_event_loop()
            # 将这个新创建的循环设置为当前线程的事件循环
            asyncio.set_event_loop(self.loop)
            
            # --- 修正: 循环创建后设置事件，通知主线程 loop 已就绪 ---
            # 这是关键的同步步骤。一旦 self.loop 被赋值，就立即设置事件。
            # 这将释放主线程中正在等待的 .wait() 调用，使其可以安全地使用 self.loop。
            self._loop_ready_event.set()
            
            # 启动事件循环，它将一直运行，直到被显式停止（例如在 on_closing 方法中）
            try:
                self.loop.run_forever()
            finally:
                # 当循环结束时（通常在程序退出时），确保它被正确关闭
                # 获取所有正在运行的任务并取消它们
                tasks = asyncio.all_tasks(loop=self.loop)
                for task in tasks:
                    task.cancel()
                
                # 收集所有任务的取消结果
                async def gather_tasks():
                    await asyncio.gather(*tasks, return_exceptions=True)

                # 在循环中运行任务收集，直到完成
                self.loop.run_until_complete(gather_tasks())
                self.loop.close()
                logger.info("Asyncio event loop has been properly shut down.")

        # 创建一个新的守护线程来运行 run_loop 函数。
        # 设置为守护线程 (daemon=True) 意味着如果主程序退出，这个线程也会被强制终止。
        self.async_loop_thread = threading.Thread(target=run_loop, daemon=True, name="AsyncioEventLoopThread")
        
        # 启动后台线程
        self.async_loop_thread.start()
        
        # 记录日志，表示后台循环线程已启动
        logger.info("Asyncio event loop started in a separate thread.")

    
    def setup_window(self):
        """设置窗口"""
        # ### 修正：从窗口标题中移除已被淘汰的 FSRCNN ###
        self.root.title(f"CVOCR增强版v{CVOCRConstants.VERSION} - 高精度文本识别 (PP-OCRv3+LayoutLMv2+Tesseract+GPT-Neo+TransformerOCR)  作者：跳舞的火公子")
        self.root.geometry("1800x1200")
        self.root.minsize(1600, 1000)
        
        # 设置样式
        self.style_manager = ttk.Style()
        design.configure_ttk_styles(self.style_manager)
        
        self.root.configure(bg=design.get_color('neutral', '50'))

        if self._is_standalone:
            self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # 设置图标（如果存在）
        try:
            if os.path.exists('cvocr_icon.ico'):
                self.root.iconbitmap('cvocr_icon.ico')
        except Exception:
            pass
    
    def create_widgets(self):
        """创建主要控件"""
        main_frame = tk.Frame(self.root, bg=design.get_color('neutral', '50'))
        main_frame.pack(fill='both', expand=True, 
                        padx=design.get_spacing('4'), 
                        pady=design.get_spacing('3'))
        
        # 左侧控制面板
        self.create_enhanced_control_panel(main_frame)
        
        # 右侧显示区域
        self.create_display_area(main_frame)
    def _create_segmentation_techniques_section(self):
        """
        创建高级文本分割技术选择区 (V2 - LayoutLMv2集成版)
        - 在“智能行合并”下增加“使用LayoutLMv2进行语义合并”的子选项，
          为用户提供几何合并与语义合并两种模式的选择。
        - 增强了Tooltip提示，以清晰地解释每个选项的功能和适用场景。
        """
        # --- 主容器 ---
        seg_frame = ttk.LabelFrame(self.inner_control_frame, text="高级文本分割技术", padding=design.get_spacing('3'))
        seg_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # --- 功能描述标签 ---
        desc_label = ttk.Label(seg_frame, text="自由组合检测算法以适应不同图像。选择引擎精度预设可自动配置。", 
                               font=design.get_font('xs'), foreground='gray', wraplength=380, justify='left')
        desc_label.pack(anchor='w', pady=(0, design.get_spacing('2')))

        # --- 定义所有可用的分割技术及其描述 ---
        techniques = [
            ('seg_simple_high_contrast', '高对比度轮廓 (快, 适用于清晰文档)'),
            ('seg_improved_mser', '改进MSER (通用, 鲁棒)'),
            ('seg_multiscale_contour', '多尺度轮廓 (适合多尺寸文本)'),
            ('seg_gradient_based', '梯度检测 (适合边缘模糊文本)'),
            ('seg_multilevel_mser', '多级MSER (极精确, 耗时)'),
            ('seg_stroke_width_transform', '笔画宽度变换 (SWT, 复杂场景)'),
            ('seg_connected_components', '连通分量分析 (字符级, 精细)'),
            ('seg_character_level', '字符级分割 (实验性, 耗时)')
        ]

        # --- 循环创建技术选择的复选框 ---
        for var_name, text in techniques:
            ttk.Checkbutton(seg_frame, text=text,
                            variable=self.settings[var_name], style='TCheckbutton').pack(anchor='w')

        # --- 分隔线 ---
        ttk.Separator(seg_frame, orient='horizontal').pack(fill='x', pady=design.get_spacing('2'), padx=design.get_spacing('1'))
        
        # --- 智能行合并控制区域 ---
        merge_control_frame = ttk.Frame(seg_frame)
        merge_control_frame.pack(fill='x', pady=(design.get_spacing('1'), 0))

        # “启用智能行合并” 主开关
        merge_check = ttk.Checkbutton(merge_control_frame, text="启用智能行合并",
                                      variable=self.settings['enable_smart_line_merge'])
        merge_check.pack(side='left', anchor='w')
        Tooltip(merge_check, "将检测到的相邻小文本块合并成更完整的逻辑单元（行、段落等）。\n这是所有合并功能的主开关。")
        
        # “预览合并效果” 按钮
        btn_preview_merge = tk.Button(merge_control_frame, text="🔬 预览合并效果", command=self.preview_merge_effect)
        design.apply_button_style(btn_preview_merge, 'secondary')
        btn_preview_merge.pack(side='left', padx=(design.get_spacing('2'), 0))
        Tooltip(btn_preview_merge, "预览启用此功能前后的分割框对比效果。")

        # --- 新增：LayoutLMv2 语义合并选项 ---
        # 使用一个新的框架并进行缩进，以在视觉上表示层级关系
        layoutlm_merge_frame = ttk.Frame(seg_frame)
        layoutlm_merge_frame.pack(fill='x', padx=(20, 0))

        # “使用LayoutLMv2进行语义合并” 子选项
        layoutlm_merge_check = ttk.Checkbutton(layoutlm_merge_frame, text="🧠 使用LayoutLMv2进行语义合并 (精度最高)",
                                               variable=self.settings['enable_layoutlm_merge'])
        layoutlm_merge_check.pack(anchor='w')
        Tooltip(layoutlm_merge_check, ("需要已初始化LayoutLMv2模型。\n"
                                       "启用后，将使用深度学习模型分析文档结构（段落、列表、表格），"
                                       "实现最智能的合并，能处理多栏、图文混排等复杂布局。\n"
                                       "【注意】会显著增加处理时间！"))
    def create_enhanced_control_panel(self, parent):
        """创建增强控制面板"""
        # 创建外层容器
        outer_control_frame = ttk.LabelFrame(parent, text="CVOCR增强控制面板", 
                                                padding=design.get_spacing('1'))
        outer_control_frame.pack(side='left', fill='y', padx=(0, design.get_spacing('4')))

        # 创建滚动画布
        self.control_canvas = tk.Canvas(outer_control_frame, 
                                        bg=design.get_color('neutral', '50'), 
                                        highlightthickness=0,
                                        width=400)  # 设置固定宽度
        self.control_canvas.pack(side='left', fill='both', expand=True)

        # 创建滚动条
        control_scrollbar = ttk.Scrollbar(outer_control_frame, 
                                            orient='vertical', 
                                            command=self.control_canvas.yview)
        control_scrollbar.pack(side='right', fill='y')

        self.control_canvas.configure(yscrollcommand=control_scrollbar.set)
        self.control_canvas.bind_all("<MouseWheel>", self._on_mousewheel)

        # 创建内部框架
        self.inner_control_frame = ttk.Frame(self.control_canvas, 
                                                padding=design.get_spacing('3'))
        
        self.control_canvas_window = self.control_canvas.create_window(
            (0, 0), window=self.inner_control_frame, anchor="nw", tags="inner_frame")

        self.inner_control_frame.bind("<Configure>", self._on_inner_control_frame_configure)
        self.control_canvas.bind("<Configure>", self._on_control_canvas_configure)

        # 系统状态区
        self._create_system_status_section()
        
        # CVOCR组件配置区
        self._create_cvocr_components_section()
        
        # OCR配置区
        self._create_ocr_configuration_section()

        # --- 新增调用 ---
        self._create_segmentation_techniques_section()
        
        # 图像操作区
        self._create_image_operations_section()
        
        # 文本识别操作区
        self._create_recognition_operations_section()
        
        # 高级设置区
        self._create_advanced_settings_section()
        
        # 结果操作区
        self._create_result_operations_section()
        
        # 日志区域
        self._create_log_section()
    
    def _create_system_status_section(self):
        """创建系统状态区"""
        status_frame = ttk.LabelFrame(self.inner_control_frame, text="系统状态", padding=design.get_spacing('3'))
        status_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        self.status_label = ttk.Label(status_frame, text="系统未初始化", style='Warning.TLabel')
        self.status_label.pack(pady=design.get_spacing('1'))
        
        # 系统检查按钮
        btn_system_check = tk.Button(status_frame, text="🔍 系统检查", command=self.check_system)
        design.apply_button_style(btn_system_check, 'secondary')
        btn_system_check.pack(fill='x', pady=design.get_spacing('1'))

        # 初始化CVOCR按钮
        btn_init_cvocr = tk.Button(status_frame, text="🚀 初始化CVOCR", command=self.initialize_cvocr)
        design.apply_button_style(btn_init_cvocr, 'primary')
        btn_init_cvocr.pack(fill='x', pady=design.get_spacing('1'))
        
        # 版本信息显示
        version_label = ttk.Label(status_frame, text=f"CVOCR v{CVOCRConstants.VERSION}", 
                                 style='TLabel')
        version_label.pack(pady=design.get_spacing('1'))
    
    def _create_cvocr_components_section(self):
        """
        创建CVOCR组件配置区 (V3.30 - 统一模型选择与状态反馈版)
        - 为所有主要的AI组件（LayoutLMv2, GPT-Neo, Transformer OCR）提供统一的配置UI。
        - 每个组件都包含：启用开关、功能描述、模型选择下拉框和状态反馈标签。
        - 模型列表可以从外部配置文件加载，增加了灵活性（此处为简化，仍硬编码）。
        """
        components_frame = ttk.LabelFrame(self.inner_control_frame, text="CVOCR组件配置", padding=design.get_spacing('3'))
        components_frame.pack(fill='x', pady=(0, design.get_spacing('4')))

        # --- 统一的组件创建函数，以减少代码重复 ---
        def create_component_widget(parent, check_var_name, check_text, desc_text,
                                    model_var_name, model_list, tooltip_text):
            
            # 主框架
            frame = ttk.Frame(parent)
            frame.pack(fill='x', pady=design.get_spacing('2'))

            # 启用复选框和描述
            check_frame = ttk.Frame(frame)
            check_frame.pack(fill='x')
            checkbutton = ttk.Checkbutton(check_frame, text=check_text,
                                          variable=self.settings[check_var_name],
                                          style='TCheckbutton')
            checkbutton.pack(anchor='w')
            Tooltip(checkbutton, tooltip_text) # 为复选框添加提示

            desc_label = ttk.Label(check_frame, text=desc_text,
                                   font=design.get_font('xs'), foreground='gray')
            desc_label.pack(anchor='w', padx=(20, 0)) # 缩进

            # 模型选择和状态反馈
            model_frame = ttk.Frame(frame)
            model_frame.pack(fill='x', pady=(design.get_spacing('1'), 0), padx=(20, 0)) # 缩进

            tk.Label(model_frame, text="模型选择:", bg=design.get_color('neutral', '50')).pack(side='left', padx=(0, design.get_spacing('2')))
            
            model_combo = ttk.Combobox(model_frame,
                                       textvariable=self.settings[model_var_name],
                                       values=model_list,
                                       width=30,
                                       state='readonly')
            model_combo.pack(side='left', fill='x', expand=True)

            # 创建并存储状态标签，以便后续更新
            status_label = ttk.Label(model_frame, text="(未初始化)", foreground="gray", font=design.get_font('xs'))
            status_label.pack(side='left', padx=(design.get_spacing('2'), 0))
            
            return status_label # 返回状态标签的引用

        # --- 1. LayoutLMv2 布局分析 ---
        layoutlm_models = [
            'microsoft/layoutlmv2-base-uncased',
            'microsoft/layoutlmv2-large-uncased' # 提供大模型选项
        ]
        self.layoutlm_status_label = create_component_widget(
            components_frame,
            check_var_name='enable_layout_analysis',
            check_text="📄 启用LayoutLMv2布局分析",
            desc_text="理解文档结构，提升表格、列表等复杂版面识别",
            model_var_name='layoutlm_model', # 新增一个设置变量
            model_list=layoutlm_models,
            tooltip_text="分析页面元素的类型（如标题、段落、表格），为结构化输出提供依据。"
        )
        # 为新的设置变量初始化
        if 'layoutlm_model' not in self.settings:
            self.settings['layoutlm_model'] = tk.StringVar(value=layoutlm_models[0])

        # --- 2. GPT-Neo 上下文分析 ---
        gpt_neo_models = [
            'EleutherAI/gpt-neo-125M',
            'EleutherAI/gpt-neo-1.3B' # 提供更大、更强的模型选项
        ]
        self.gpt_neo_status_label = create_component_widget(
            components_frame,
            check_var_name='enable_context_analysis',
            check_text="🧠 启用GPT-Neo上下文分析",
            desc_text="智能文本纠错，优化语法和格式，提升识别准确度",
            model_var_name='gpt_neo_model', # 新增一个设置变量
            model_list=gpt_neo_models,
            tooltip_text="利用大语言模型对OCR初步结果进行后处理，修正常见的识别错误。"
        )
        # 为新的设置变量初始化
        if 'gpt_neo_model' not in self.settings:
            self.settings['gpt_neo_model'] = tk.StringVar(value=gpt_neo_models[0])

        # --- 3. Transformer OCR (整页模式) ---
        trocr_models = [
            'microsoft/trocr-base-printed',
            'microsoft/trocr-base-handwritten',
            'microsoft/trocr-small-printed',
            'microsoft/trocr-large-printed', # 提供大模型选项
            'google/trocr-base-zh-printed'
        ]
        self.trocr_status_label = create_component_widget(
            components_frame,
            check_var_name='enable_transformer_ocr',
            check_text="🤖 启用Transformer OCR (整页模式)",
            desc_text="端到端深度学习文本识别。不与高级分割/全元素检测同时使用。",
            model_var_name='transformer_ocr_model',
            model_list=trocr_models,
            tooltip_text="直接从图像像素识别文本，适合无复杂布局的清晰图像。开启此项时，高级分割将被忽略。"
        )
    def _browse_for_yolo_file(self, setting_var: tk.StringVar, title: str, filetypes: List[Tuple[str, str]]):
        """打开文件对话框以选择YOLO模型文件。"""
        file_path = filedialog.askopenfilename(title=title, filetypes=filetypes)
        if file_path:
            setting_var.set(file_path)
            self.log_message(f"✅ 已选择{title}: {os.path.basename(file_path)}", "SUCCESS")
    
    
    
    def _create_ocr_configuration_section(self):
        """
        创建OCR配置区 (V4.7 - 增强引导与UI重构版)
        - 完全暴露OEM和PSM参数，采用直接选择逻辑。
        - 新增PSM帮助按钮和增强的Tooltip，引导用户做出正确选择。
        - 重构检测模式与识别引擎的UI布局，使其更清晰、更具功能性。
        """
        # --- 主容器 ---
        ocr_frame = ttk.LabelFrame(self.inner_control_frame, text="OCR与检测配置", padding=design.get_spacing('3'))
        ocr_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # 1. 语言设置
        lang_frame = ttk.Frame(ocr_frame)
        lang_frame.pack(fill='x', pady=design.get_spacing('1'))
        lang_label = tk.Label(lang_frame, text="识别语言:", bg=design.get_color('neutral', '50'))
        lang_label.pack(side='left', padx=(0, design.get_spacing('2')))
        lang_combo = ttk.Combobox(lang_frame, textvariable=self.settings['language'],
                                    values=['auto', 'chi_sim', 'eng', 'chi_tra', 'jpn', 'kor', 'chi_sim+eng'], 
                                    width=15, state='readonly')
        lang_combo.pack(side='right', fill='x', expand=True)
        Tooltip(lang_frame, "选择图片中包含的主要语言。\n'chi_sim+eng' 适合中英文混合的文档。")

        # 2. Tesseract 核心参数
        params_frame = ttk.LabelFrame(ocr_frame, text="Tesseract 核心参数", padding=design.get_spacing('2'))
        params_frame.pack(fill='x', pady=design.get_spacing('2'))
        
        path_frame = ttk.Frame(params_frame)
        path_frame.pack(fill='x', pady=design.get_spacing('1'), expand=True)
        path_label = tk.Label(path_frame, text="Tesseract 路径:", bg=design.get_color('neutral', '50'))
        path_label.pack(side='left')
        path_entry = ttk.Entry(path_frame, textvariable=self.settings['tesseract_path'])
        path_entry.pack(side='left', fill='x', expand=True, padx=(design.get_spacing('1'), design.get_spacing('1')))
        browse_button = ttk.Button(path_frame, text="浏览...", command=self._browse_for_tesseract)
        browse_button.pack(side='right')
        Tooltip(path_frame, "设置Tesseract OCR引擎可执行文件(tesseract.exe)的路径。\n如果系统环境变量已配置，则可留空。")

        conf_frame = ttk.Frame(params_frame)
        conf_frame.pack(fill='x', pady=design.get_spacing('1'))
        conf_label = tk.Label(conf_frame, text="结果置信度阈值:", bg=design.get_color('neutral', '50'))
        conf_label.pack(side='left')
        conf_scale = ttk.Scale(conf_frame, from_=0, to=100, variable=self.settings['confidence_threshold'], orient='horizontal', length=120)
        conf_scale.pack(side='right')
        Tooltip(conf_frame, "过滤掉置信度低于此值的识别结果。\n调高可获得更准确但可能不完整的文本，调低则相反。建议60-85。")
        
        # --- 全新的 PSM (页面分割模式) UI ---
        psm_frame = ttk.Frame(params_frame)
        psm_frame.pack(fill='x', pady=design.get_spacing('1'))
        psm_label = tk.Label(psm_frame, text="页面分割模式 (PSM):", bg=design.get_color('neutral', '50'))
        psm_label.pack(side='left')
        
        psm_help_button = tk.Button(psm_frame, text="?", command=self._show_psm_help, 
                                    font=('Arial', 8, 'bold'), relief='flat', 
                                    bg=design.get_color('neutral', '200'), 
                                    activebackground=design.get_color('neutral', '300'))
        psm_help_button.pack(side='right', padx=(5,0))
        Tooltip(psm_help_button, "点击查看所有页面分割模式的详细解释。")

        psm_values = [
            "0: 方向和脚本检测(OSD)", "1: 自动页面分割+OSD", "2: 自动页面分割(无OSD)",
            "3: 全自动页面分割(默认)", "4: 假设为单列可变大小文本", "5: 假设为单个统一的垂直文本块",
            "6: 假设为单个统一的文本块", "7: 将图像视为单行文本", "8: 将图像视为单个单词",
            "9: 将图像视为圆圈内的单个单词", "10: 将图像视为单个字符",
            "11: 稀疏文本", "12: 带OSD的稀疏文本", "13: 原始行(无分词等处理)"
        ]
        psm_combo = ttk.Combobox(psm_frame, textvariable=self.settings['psm_mode'], values=psm_values, state='readonly')
        psm_combo.pack(side='right', fill='x', expand=True)
        psm_combo.set("6: 假设为单个统一的文本块") #【重要】将默认值改为对分割后最友好的模式6
        Tooltip(psm_frame, ("指导Tesseract如何分析页面布局。\n"
                           "重要提示：在启用高级分割/全元素检测后，此设置将应用于【每个】被切割出的独立文本块。\n"
                           "为获得最佳效果，强烈推荐选择区域级模式，如 6 或 7。"))

        # --- 全新的 OEM (引擎模式) UI ---
        oem_frame = ttk.LabelFrame(params_frame, text="OEM (引擎模式) - 可多选", padding=design.get_spacing('2'))
        oem_frame.pack(fill='x', pady=design.get_spacing('2'))
        
        self.settings['oem_options'] = {
            '0': tk.BooleanVar(value=False),
            '1': tk.BooleanVar(value=False),
            '2': tk.BooleanVar(value=False),
            '3': tk.BooleanVar(value=True), # 默认勾选推荐的 OEM 3
        }
        
        oem_defs = {
            '0': ("经典引擎 (Legacy)", "速度最快，基于传统模式匹配，适合极清晰的打印体。"),
            '1': ("神经网络 (LSTM)", "现代AI引擎，准确率高，但比经典引擎慢。"),
            '2': ("经典 + LSTM", "组合两个引擎，速度最慢，用于实验性比较。"),
            '3': ("默认 (推荐)", "智能选择LSTM引擎，是速度和准确率的最佳平衡点。")
        }
        
        oem_info_label = ttk.Label(oem_frame, text="勾选要使用的识别引擎。若不选，将不指定OEM参数，由Tesseract决定。",
                                   font=design.get_font('xs'), foreground='gray', wraplength=380)
        oem_info_label.pack(anchor='w', pady=(0, design.get_spacing('2')))

        checkbox_frame = ttk.Frame(oem_frame)
        checkbox_frame.pack(fill='x')
        for key, var in self.settings['oem_options'].items():
            oem_check = ttk.Checkbutton(checkbox_frame, text=oem_defs[key][0], variable=var)
            oem_check.pack(anchor='w') 
            Tooltip(oem_check, oem_defs[key][1])
            
        # 3. 检测模式与引擎配置
        detection_frame = ttk.LabelFrame(ocr_frame, text="检测模式与引擎", padding=design.get_spacing('2'))
        detection_frame.pack(fill='x', pady=design.get_spacing('2'), padx=design.get_spacing('1'))
        
        yolo_checkbox = ttk.Checkbutton(detection_frame, text="✨ 启用全元素检测 (YOLO)",
                        variable=self.settings['enable_advanced_segmentation'], 
                        style='TCheckbutton')
        yolo_checkbox.pack(anchor='w', pady=(design.get_spacing('1'), 0))
        Tooltip(yolo_checkbox, "核心模式切换！\n"
                               "▶ 勾选: 同时检测文本、表格和图形，适合复杂版面。\n"
                               "▶ 不勾选: 仅进行纯文本OCR，速度更快，适合普通文档。")
        
        desc_label = ttk.Label(detection_frame, text="    勾选此项以检测图形和表格，否则仅进行纯文本OCR。", 
                               font=design.get_font('xs'), foreground='gray', justify='left')
        desc_label.pack(anchor='w', pady=(0, design.get_spacing('2')))

        # A. 纯文本检测引擎 (默认模式) -> 不再需要，因为高级分割技术已经接管
        
        # B. 全元素检测引擎 (YOLO)
        yolo_frame = ttk.LabelFrame(detection_frame, text="全元素检测引擎 (YOLO)", padding=design.get_spacing('2'))
        yolo_frame.pack(fill='x', pady=design.get_spacing('1'))
        Tooltip(yolo_frame, "当'启用全元素检测'被勾选时使用此引擎。\n它是一个通用的对象检测器，能识别文本块、表格、图表等多种页面元素。")
        
        weights_row = ttk.Frame(yolo_frame)
        weights_row.pack(fill='x', pady=2)
        tk.Label(weights_row, text="权重 (.weights):", bg=design.get_color('neutral', '50'), width=15, anchor='w').pack(side='left')
        weights_entry = ttk.Entry(weights_row, textvariable=self.settings['yolo_weights_path'])
        weights_entry.pack(side='left', fill='x', expand=True, padx=5)
        ttk.Button(weights_row, text="浏览...", command=lambda: self._browse_for_yolo_file(
            self.settings['yolo_weights_path'], "选择权重文件", [("Weights files", "*.weights"), ("All files", "*.*")])).pack(side='right')
        Tooltip(weights_row, "YOLO模型的'大脑'，包含了所有通过训练学到的知识。")

        cfg_row = ttk.Frame(yolo_frame)
        cfg_row.pack(fill='x', pady=2)
        tk.Label(cfg_row, text="配置 (.cfg):", bg=design.get_color('neutral', '50'), width=15, anchor='w').pack(side='left')
        cfg_entry = ttk.Entry(cfg_row, textvariable=self.settings['yolo_cfg_path'])
        cfg_entry.pack(side='left', fill='x', expand=True, padx=5)
        ttk.Button(cfg_row, text="浏览...", command=lambda: self._browse_for_yolo_file(
            self.settings['yolo_cfg_path'], "选择配置文件", [("Config files", "*.cfg"), ("All files", "*.*")])).pack(side='right')
        Tooltip(cfg_row, "YOLO模型的'蓝图'，定义了神经网络的结构。")

        names_row = ttk.Frame(yolo_frame)
        names_row.pack(fill='x', pady=2)
        tk.Label(names_row, text="类别 (.names):", bg=design.get_color('neutral', '50'), width=15, anchor='w').pack(side='left')
        names_entry = ttk.Entry(names_row, textvariable=self.settings['yolo_names_path'])
        names_entry.pack(side='left', fill='x', expand=True, padx=5)
        ttk.Button(names_row, text="浏览...", command=lambda: self._browse_for_yolo_file(
            self.settings['yolo_names_path'], "选择类别文件", [("Names files", "*.names"), ("All files", "*.*")])).pack(side='right')
        Tooltip(names_row, "一个简单的文本文件，列出了YOLO模型能够识别的所有对象名称。")
        
        # C. 文本块识别引擎
        recognizer_frame = ttk.LabelFrame(ocr_frame, text="文本块识别引擎", padding=design.get_spacing('2'))
        recognizer_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        tesseract_row = ttk.Frame(recognizer_frame)
        tesseract_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        
        tess_radio = ttk.Radiobutton(tesseract_row, text="Tesseract", variable=self.settings['segmentation_recognizer'], value="Tesseract")
        tess_radio.pack(side='left', padx=(0, design.get_spacing('2')))
        
        tess_fine_tune_check = ttk.Checkbutton(tesseract_row, text="启用精细化预处理", variable=self.settings['enable_tesseract_fine_tuning'])
        tess_fine_tune_check.pack(side='left', padx=(0, design.get_spacing('2')))
        Tooltip(tess_fine_tune_check, "对每个文本块进行缩放、增强、二值化等操作，通常能提升Tesseract识别率。")

        btn_preview_region_proc = tk.Button(tesseract_row, text="🔬 预览", command=self.preview_region_preprocessing)
        design.apply_button_style(btn_preview_region_proc, 'secondary')
        btn_preview_region_proc.pack(side='left')
        Tooltip(btn_preview_region_proc, "预览精细化预处理对单个文本区域的效果。")

        trocr_row = ttk.Frame(recognizer_frame)
        trocr_row.pack(fill='x', pady=(design.get_spacing('1'), 0))

        trocr_radio = ttk.Radiobutton(trocr_row, text="TransformerOCR", variable=self.settings['segmentation_recognizer'], value="TransformerOCR")
        trocr_radio.pack(side='left', padx=(0, design.get_spacing('2')))

        trocr_models = [
            'microsoft/trocr-base-printed',
            'microsoft/trocr-base-handwritten',
            'microsoft/trocr-large-printed',
            'google/trocr-base-zh-printed'
        ]
        trocr_model_combo = ttk.Combobox(trocr_row, 
                                         textvariable=self.settings['transformer_ocr_model'],
                                         values=trocr_models, 
                                         width=30, 
                                         state='readonly')
        trocr_model_combo.pack(side='left', fill='x', expand=True, padx=(0, design.get_spacing('1')))
        
        self.trocr_model_status_label = ttk.Label(trocr_row, text=" (未初始化)", foreground="gray")
        self.trocr_model_status_label.pack(side='left')
        
        recognizer_desc = ttk.Label(recognizer_frame, text="选择用于识别已定位文本块的引擎。TransformerOCR精度更高，但需加载模型。", 
                                   font=design.get_font('xs'), foreground='gray', justify='left', wraplength=350)
        recognizer_desc.pack(anchor='w', pady=(design.get_spacing('2'), 0))
    def _show_psm_help(self):
        """创建一个新窗口，用表格详细解释所有PSM模式。"""
        help_window = tk.Toplevel(self.root)
        help_window.title("页面分割模式 (PSM) 详细说明")
        help_window.geometry("700x550")
        help_window.transient(self.root)
        help_window.grab_set()

        main_frame = ttk.Frame(help_window, padding=design.get_spacing('4'))
        main_frame.pack(fill='both', expand=True)

        title_label = tk.Label(main_frame, text="Tesseract 页面分割模式 (PSM)", bg=design.get_color('neutral', '50'))
        design.apply_text_style(title_label, 'h3')
        title_label.pack(anchor='w', pady=(0, design.get_spacing('2')))
        
        desc_label = tk.Label(main_frame, bg=design.get_color('neutral', '50'),
                              text=("PSM指导Tesseract如何分析和分割页面布局。\n"
                                    "在启用高级分割后，此设置将应用于【每一个】被切割出的独立文本块。\n"
                                    "因此，选择正确的模式至关重要！"),
                              wraplength=650, justify='left', font=design.get_font('body', family='primary'))
        desc_label.pack(anchor='w', pady=(0, design.get_spacing('4')))

        # 使用Treeview创建一个表格
        columns = ('模式', '说明', '适用场景')
        tree = ttk.Treeview(main_frame, columns=columns, show='headings', height=15)
        
        tree.heading('模式', text='模式 (值)')
        tree.column('模式', width=100, anchor='center')
        tree.heading('说明', text='说明')
        tree.column('说明', width=300, anchor='w')
        tree.heading('适用场景', text='推荐场景')
        tree.column('适用场景', width=250, anchor='w')

        full_psm_data = [
            ("0", "方向和脚本检测 (OSD)", "仅用于检测文字方向和语言，不进行OCR。"),
            ("1", "自动页面分割 + OSD", "【不推荐】用于已分割区域。"),
            ("2", "自动页面分割 (无OSD)", "【不推荐】用于已分割区域。"),
            ("3", "全自动页面分割 (默认)", "【不推荐】用于已分割区域。"),
            ("4", "假设为单列可变大小文本", "【不推荐】用于已分割区域。"),
            ("5", "假设为单个统一的垂直文本块", "【特定场景】用于垂直书写的文本块。"),
            ("6", "假设为单个统一的文本块", "【强烈推荐】最通用的模式。"),
            ("7", "将图像视为单行文本", "【推荐】用于单行文字。"),
            ("8", "将图像视为单个单词", "【推荐】用于单个单词。"),
            ("9", "将图像视为圆圈内的单个单词", "特定场景，如印章。"),
            ("10", "将图像视为单个字符", "特定场景，如验证码。"),
            ("11", "稀疏文本", "【不推荐】用于已分割区域。"),
            ("12", "带OSD的稀疏文本", "【不推荐】用于已分割区域。"),
            ("13", "原始行", "【推荐】用于序列号等。")
        ]

        for item in full_psm_data:
            tree.insert('', 'end', values=item)

        tree.pack(fill='both', expand=True)

        close_button = tk.Button(main_frame, text="关闭", command=help_window.destroy)
        design.apply_button_style(close_button, 'primary')
        close_button.pack(pady=(design.get_spacing('4'), 0))
    
    
    def _create_image_operations_section(self):
        """创建图像操作区"""
        image_frame = ttk.LabelFrame(self.inner_control_frame, text="图像操作", padding=design.get_spacing('3'))
        image_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        btn_select_image = tk.Button(image_frame, text="📁 选择图片", command=self.select_image)
        design.apply_button_style(btn_select_image, 'secondary')
        btn_select_image.pack(fill='x', pady=design.get_spacing('1'))

        btn_preview_process = tk.Button(image_frame, text="🔬 预览预处理", command=self.preview_preprocessing)
        design.apply_button_style(btn_preview_process, 'primary')
        btn_preview_process.pack(fill='x', pady=design.get_spacing('1'))

        # --- 新增代码开始 ---
        btn_preview_segmentation = tk.Button(image_frame, text="📊 预览分割结果", command=self.preview_segmentation)
        design.apply_button_style(btn_preview_segmentation, 'primary')
        btn_preview_segmentation.pack(fill='x', pady=design.get_spacing('1'))
        # --- 新增代码结束 ---
        
        btn_generate_test = tk.Button(image_frame, text="🎨 生成测试图片", command=self.generate_test_images)
        design.apply_button_style(btn_generate_test, 'secondary')
        btn_generate_test.pack(fill='x', pady=design.get_spacing('1'))
        
        btn_batch_select = tk.Button(image_frame, text="📁 批量选择", command=self.select_batch_images)
        design.apply_button_style(btn_batch_select, 'secondary')
        btn_batch_select.pack(fill='x', pady=design.get_spacing('1'))
    
    def _create_recognition_operations_section(self):
        """创建文本识别操作区"""
        recognition_frame = ttk.LabelFrame(self.inner_control_frame, text="文本识别", padding=design.get_spacing('3'))
        recognition_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # --- 按钮1: 高级CVOCR识别 ---
        btn_start_recognition = tk.Button(recognition_frame, text="🚀 高级CVOCR识别", command=self.start_enhanced_recognition)
        design.apply_button_style(btn_start_recognition, 'primary')
        btn_start_recognition.pack(fill='x', pady=design.get_spacing('1'))
        
        # 中文注释
        advanced_desc = ttk.Label(recognition_frame, 
                                  text="（推荐）使用您配置的所有高级预处理和分割技术，精度最高。",
                                  font=design.get_font('xs'), foreground='gray', wraplength=380, justify='left')
        advanced_desc.pack(anchor='w', pady=(0, design.get_spacing('2')))

        # --- 按钮2: 批量处理 ---
        btn_batch_process = tk.Button(recognition_frame, text="⚡ 批量处理", command=self.batch_process)
        design.apply_button_style(btn_batch_process, 'secondary')
        btn_batch_process.pack(fill='x', pady=design.get_spacing('1'))
        
        # --- 按钮3: 快速CVOCR识别 ---
        btn_quick_ocr = tk.Button(recognition_frame, text="⚡ 快速CVOCR识别", command=self.quick_ocr)
        design.apply_button_style(btn_quick_ocr, 'secondary')
        btn_quick_ocr.pack(fill='x', pady=design.get_spacing('1'))
        
        # 中文注释
        quick_desc = ttk.Label(recognition_frame, 
                               text="（快速）跳过所有复杂处理，直接调用Tesseract进行端到端识别。",
                               font=design.get_font('xs'), foreground='gray', wraplength=380, justify='left')
        quick_desc.pack(anchor='w', pady=(0, design.get_spacing('2')))
    
    def _create_advanced_settings_section(self):
        """
        创建高级设置区（V4.1 - 完全手动控制 & 预设管理版）。
        - 为所有预处理操作添加独立的启用/禁用复选框。
        - 移除所有后台自动策略，流程完全由用户勾选决定。
        - 新增预设保存与加载功能。
        - 新增对核心转换步骤（灰度、二值化）的控制。
        """
        advanced_frame = ttk.LabelFrame(self.inner_control_frame, text="高级设置", padding=design.get_spacing('3'))
        advanced_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # --- 预设管理 ---
        preset_frame = ttk.LabelFrame(advanced_frame, text="预设管理", padding=design.get_spacing('2'))
        preset_frame.pack(fill='x', pady=design.get_spacing('1'), padx=design.get_spacing('1'))
        
        btn_save_preset = tk.Button(preset_frame, text="💾 保存当前预设", command=self._save_preset_dialog)
        design.apply_button_style(btn_save_preset, 'secondary')
        btn_save_preset.pack(side='left', padx=(0, design.get_spacing('2')))

        btn_load_preset = tk.Button(preset_frame, text="📂 加载预设", command=self._load_preset_dialog)
        design.apply_button_style(btn_load_preset, 'secondary')
        btn_load_preset.pack(side='left')
        
        # --- 预处理总开关 ---
        preprocessing_frame = ttk.LabelFrame(advanced_frame, text="图像预处理选项", padding=design.get_spacing('2'))
        preprocessing_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(preprocessing_frame, text="🔧 启用预处理 (总开关)",
                        variable=self.settings['enable_preprocessing'], style='TCheckbutton').pack(anchor='w')
        
        ttk.Separator(preprocessing_frame, orient='horizontal').pack(fill='x', pady=design.get_spacing('2'))

        # --- 几何校正组 (现在每个都有自己的开关) ---
        geo_frame = ttk.LabelFrame(preprocessing_frame, text="几何校正", padding=design.get_spacing('2'))
        geo_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        deskew_row = ttk.Frame(geo_frame)
        deskew_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        ttk.Checkbutton(deskew_row, text="📐 倾斜校正", variable=self.settings['enable_deskew'], style='TCheckbutton').pack(side='left')
        ttk.Label(deskew_row, text="角度阈值:").pack(side='left', padx=(design.get_spacing('4'), design.get_spacing('1')))
        ttk.Scale(deskew_row, from_=0.1, to=5.0, variable=self.settings['deskew_angle_threshold'], orient='horizontal', length=100).pack(side='left')
        
        border_row = ttk.Frame(geo_frame)
        border_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        ttk.Checkbutton(border_row, text="🖼️ 移除边框", variable=self.settings['remove_borders'], style='TCheckbutton').pack(side='left')
        ttk.Label(border_row, text="边框阈值:").pack(side='left', padx=(design.get_spacing('4'), design.get_spacing('1')))
        ttk.Scale(border_row, from_=0, to=100, variable=self.settings['border_threshold'], orient='horizontal', length=100).pack(side='left')
        
        ttk.Checkbutton(geo_frame, text="✂️ 裁剪到内容", variable=self.settings['crop_to_content'], style='TCheckbutton').pack(anchor='w')
        ttk.Checkbutton(geo_frame, text="📄 页面边框检测", variable=self.settings['page_border_detection'], style='TCheckbutton').pack(anchor='w')

        # --- 图像增强与降噪组 (现在每个都有自己的开关) ---
        enhance_frame = ttk.LabelFrame(preprocessing_frame, text="图像增强与降噪", padding=design.get_spacing('2'))
        enhance_frame.pack(fill='x', pady=design.get_spacing('1'))

        ttk.Checkbutton(enhance_frame, text="🌫️ 阴影移除", variable=self.settings['shadow_removal'], style='TCheckbutton').pack(anchor='w')
        
        bilateral_row = ttk.Frame(enhance_frame)
        bilateral_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        ttk.Checkbutton(bilateral_row, text="💧 双边滤波", variable=self.settings['bilateral_filter'], style='TCheckbutton').pack(side='left')
        ttk.Label(bilateral_row, text="直径:").pack(side='left', padx=(design.get_spacing('2'), design.get_spacing('1')))
        ttk.Scale(bilateral_row, from_=1, to=15, variable=self.settings['bilateral_d'], orient='horizontal', length=60).pack(side='left')
        
        ttk.Checkbutton(enhance_frame, text="📈 直方图均衡化", variable=self.settings['histogram_equalization'], style='TCheckbutton').pack(anchor='w')
        
        clahe_row = ttk.Frame(enhance_frame)
        clahe_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        ttk.Checkbutton(clahe_row, text="🔆 CLAHE增强", variable=self.settings['apply_clahe'], style='TCheckbutton').pack(side='left')
        ttk.Label(clahe_row, text="裁剪限制:").pack(side='left', padx=(design.get_spacing('2'), design.get_spacing('1')))
        ttk.Scale(clahe_row, from_=1.0, to=5.0, variable=self.settings['clahe_clip_limit'], orient='horizontal', length=80).pack(side='left')

        unsharp_row = ttk.Frame(enhance_frame)
        unsharp_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        ttk.Checkbutton(unsharp_row, text="✨ 反锐化掩模", variable=self.settings['unsharp_mask'], style='TCheckbutton').pack(side='left')
        ttk.Label(unsharp_row, text="半径:").pack(side='left', padx=(design.get_spacing('2'), design.get_spacing('1')))
        ttk.Scale(unsharp_row, from_=0.5, to=5.0, variable=self.settings['unsharp_radius'], orient='horizontal', length=80).pack(side='left')
        ttk.Label(unsharp_row, text="强度:").pack(side='left', padx=(design.get_spacing('2'), design.get_spacing('1')))
        ttk.Scale(unsharp_row, from_=0.0, to=3.0, variable=self.settings['unsharp_amount'], orient='horizontal', length=80).pack(side='left')
        
        # --- 核心转换步骤控制 ---
        core_conversion_frame = ttk.LabelFrame(preprocessing_frame, text="核心转换步骤", padding=design.get_spacing('2'))
        core_conversion_frame.pack(fill='x', pady=design.get_spacing('1'))

        ttk.Checkbutton(core_conversion_frame, text="⚙️ 转换为灰度图", 
                        variable=self.settings['enable_grayscale'], style='TCheckbutton').pack(anchor='w')
        
        binarization_row = ttk.Frame(core_conversion_frame)
        binarization_row.pack(fill='x', pady=(0, design.get_spacing('1')))
        ttk.Checkbutton(binarization_row, text="⚫⚪ 二值化", 
                        variable=self.settings['enable_binarization'], style='TCheckbutton').pack(side='left')

        ttk.Label(binarization_row, text="块大小:").pack(side='left', padx=(design.get_spacing('4'), design.get_spacing('1')))
        ttk.Scale(binarization_row, from_=3, to=35, variable=self.settings['adaptive_block_size'], orient='horizontal', length=80).pack(side='left')
        ttk.Label(binarization_row, text="C值:").pack(side='left', padx=(design.get_spacing('2'), design.get_spacing('1')))
        ttk.Scale(binarization_row, from_=0, to=15, variable=self.settings['adaptive_c_constant'], orient='horizontal', length=80).pack(side='left')

        # --- 显示与保存设置 ---
        display_frame = ttk.LabelFrame(advanced_frame, text="显示与保存设置", padding=design.get_spacing('2'))
        display_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(display_frame, text="📊 在结果表格中显示置信度",
                        variable=self.settings['show_confidence'], style='TCheckbutton').pack(anchor='w')
        ttk.Checkbutton(display_frame, text="💾 自动保存识别结果 (JSON)",
                        variable=self.settings['auto_save_results'], style='TCheckbutton').pack(anchor='w')
        
        # --- 性能设置 ---
        performance_frame = ttk.LabelFrame(advanced_frame, text="性能设置", padding=design.get_spacing('2'))
        performance_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(performance_frame, text="🖥️ 使用GPU加速 (需PyTorch GPU版)",
                        variable=self.settings['use_gpu'], style='TCheckbutton').pack(anchor='w')
    
    
    
    def _save_preset_dialog(self):
        """打开对话框让用户命名并保存当前预设。
        此版本会保存所有预处理相关的设置，包括新的高级分割技术选项。
        """
        from tkinter import simpledialog
        preset_name = simpledialog.askstring("保存预设", "请输入预设名称:", parent=self.root)
        
        if preset_name:
            try:
                # 收集所有与预处理和分割技术相关的设置值
                preset_settings = {}
                
                # 定义一个完整的列表，包含所有需要保存到预设中的设置项的键
                preset_keys = [
                    # 预处理总开关
                    'enable_preprocessing',
                    
                    # 几何校正
                    'enable_deskew', 
                    'deskew_angle_threshold', 
                    'remove_borders', 
                    'border_threshold', 
                    'crop_to_content', 
                    'page_border_detection', 
                    
                    # 图像增强与降噪
                    'shadow_removal',
                    'bilateral_filter', 
                    'bilateral_d', 
                    'histogram_equalization', 
                    'apply_clahe',
                    'clahe_clip_limit', 
                    'unsharp_mask', 
                    'unsharp_radius', 
                    'unsharp_amount',
                    
                    # 核心转换步骤
                    'enable_grayscale', 
                    'enable_binarization',
                    'adaptive_block_size', 
                    'adaptive_c_constant',
                    
                    # 高级分割技术选项
                    'seg_simple_high_contrast', 
                    'seg_improved_mser', 
                    'seg_multiscale_contour',
                    'seg_gradient_based', 
                    'seg_multilevel_mser', 
                    'seg_stroke_width_transform',
                    'seg_connected_components', 
                    'seg_character_level'
                ]
                
                # 遍历列表，从 self.settings 字典中获取每个设置的当前值
                for key in preset_keys:
                    if key in self.settings:
                        preset_settings[key] = self.settings[key].get()

                # 读取现有的预设文件（如果存在），以便在不覆盖其他预设的情况下添加或更新
                presets = {}
                if os.path.exists('cvocr_presets.json'):
                    with open('cvocr_presets.json', 'r', encoding='utf-8') as f:
                        try:
                            presets = json.load(f)
                        except json.JSONDecodeError:
                            # 如果文件损坏或为空，则忽略旧内容
                            pass
                
                # 更新或添加当前要保存的预设
                presets[preset_name] = preset_settings
                
                # 将更新后的所有预设写回文件
                with open('cvocr_presets.json', 'w', encoding='utf-8') as f:
                    json.dump(presets, f, indent=2, ensure_ascii=False)
                
                self.log_message(f"💾 预设 '{preset_name}' 已保存。", 'SUCCESS')
                messagebox.showinfo("保存成功", f"预设 '{preset_name}' 已成功保存！")
                
            except Exception as e:
                self.log_message(f"❌ 保存预设失败: {e}", 'ERROR')
                messagebox.showerror("保存失败", f"保存预设失败: {e}")
    def _load_preset_dialog(self):
        """打开对话框让用户选择并加载预设"""
        if not os.path.exists('cvocr_presets.json'):
            messagebox.showinfo("无预设", "没有找到已保存的预设文件。")
            return

        try:
            with open('cvocr_presets.json', 'r', encoding='utf-8') as f:
                presets = json.load(f)
            
            if not presets:
                messagebox.showinfo("无预设", "预设文件为空。")
                return

            # 创建一个选择窗口
            load_window = tk.Toplevel(self.root)
            load_window.title("加载预设")
            load_window.geometry("300x400")
            load_window.transient(self.root)
            load_window.grab_set()

            tk.Label(load_window, text="请选择一个预设加载:").pack(pady=10)
            
            listbox = tk.Listbox(load_window)
            listbox.pack(fill='both', expand=True, padx=10, pady=5)
            for name in presets.keys():
                listbox.insert(tk.END, name)

            def on_load():
                selected_indices = listbox.curselection()
                if not selected_indices:
                    return
                
                selected_name = listbox.get(selected_indices[0])
                settings_to_load = presets[selected_name]
                
                # 应用加载的设置到UI
                for key, value in settings_to_load.items():
                    if key in self.settings:
                        self.settings[key].set(value)
                
                self.log_message(f"📂 预设 '{selected_name}' 已加载。", 'SUCCESS')
                load_window.destroy()

            load_button = tk.Button(load_window, text="加载", command=on_load)
            design.apply_button_style(load_button, 'primary')
            load_button.pack(pady=10)

        except Exception as e:
            self.log_message(f"❌ 加载预设失败: {e}", 'ERROR')
            messagebox.showerror("加载失败", f"加载预设失败: {e}")
    def _create_result_operations_section(self):
        """创建结果操作区"""
        result_frame = ttk.LabelFrame(self.inner_control_frame, text="结果操作", padding=design.get_spacing('3'))
        result_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        btn_show_vis = tk.Button(result_frame, text="📊 显示可视化", command=self.show_visualization)
        design.apply_button_style(btn_show_vis, 'secondary')
        btn_show_vis.pack(fill='x', pady=design.get_spacing('1'))

        btn_export_results = tk.Button(result_frame, text="📤 导出结果", command=self.export_current_results)
        design.apply_button_style(btn_export_results, 'secondary')
        btn_export_results.pack(fill='x', pady=design.get_spacing('1'))

        btn_clear_results = tk.Button(result_frame, text="🧹 清空结果", command=self.clear_results)
        design.apply_button_style(btn_clear_results, 'secondary')
        btn_clear_results.pack(fill='x', pady=design.get_spacing('1'))
        
        btn_compare_results = tk.Button(result_frame, text="🔄 比较结果", command=self.compare_results)
        design.apply_button_style(btn_compare_results, 'secondary')
        btn_compare_results.pack(fill='x', pady=design.get_spacing('1'))
    
    def _create_log_section(self):
        """创建日志区域"""
        log_frame = ttk.LabelFrame(self.inner_control_frame, text="日志信息", padding=design.get_spacing('3'))
        log_frame.pack(fill='both', expand=True)
        
        # 日志控制按钮
        log_control_frame = ttk.Frame(log_frame)
        log_control_frame.pack(fill='x', pady=(0, design.get_spacing('2')))
        
        btn_clear_log = tk.Button(log_control_frame, text="清除日志", command=self.clear_log)
        design.apply_button_style(btn_clear_log, 'secondary')
        btn_clear_log.pack(side='left', padx=(0, design.get_spacing('2')))
        
        btn_save_log = tk.Button(log_control_frame, text="保存日志", command=self.save_log)
        design.apply_button_style(btn_save_log, 'secondary')
        btn_save_log.pack(side='left')
        
        # 日志文本区域
        self.log_text = scrolledtext.ScrolledText(log_frame, height=15, width=40,
                                                    font=design.get_font('sm', family='primary'),
                                                    bg=design.get_color('neutral', '0'),
                                                    fg=design.get_color('neutral', '800'),
                                                    relief='flat', bd=1,
                                                    highlightbackground=design.get_color('neutral', '300'),
                                                    highlightthickness=1,
                                                    wrap='word')
        self.log_text.pack(fill='both', expand=True, padx=design.get_spacing('2'), pady=design.get_spacing('2'))
        self.log_text.config(state='disabled')
    
    def _on_inner_control_frame_configure(self, event):
        """内部框架配置事件"""
        self.control_canvas.configure(scrollregion=self.control_canvas.bbox("all"))

    def _on_control_canvas_configure(self, event):
        """画布配置事件"""
        self.control_canvas.itemconfigure(self.control_canvas_window, width=event.width)

    def _on_mousewheel(self, event):
        """鼠标滚轮事件"""
        if sys.platform == "win32" or sys.platform == "darwin":
            self.control_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        else:
            if event.num == 4:
                self.control_canvas.yview_scroll(-1, "units")
            elif event.num == 5:
                self.control_canvas.yview_scroll(1, "units")
    
    def create_display_area(self, parent):
        """创建显示区域"""
        display_frame = ttk.Frame(parent)
        display_frame.pack(side='right', fill='both', expand=True)
        
        self.notebook = ttk.Notebook(display_frame)
        self.notebook.pack(fill='both', expand=True)
        
        # 图片预览标签页
        self.create_image_tab()
        
        # 识别结果标签页
        self.create_text_results_tab()
        
        # 纯文本标签页
        self.create_text_tab()
        
        # 历史记录标签页
        self.create_history_tab()
        
        # 统计信息标签页
        self.create_stats_tab()
        
        # 比较分析标签页
        self.create_comparison_tab()
   
    def create_image_tab(self):
        """创建图片预览标签页"""
        image_frame = ttk.Frame(self.notebook, padding=design.get_spacing('4'))
        self.notebook.add(image_frame, text="🖼️ 图片预览")
        
        # 图片信息框架
        info_frame = ttk.Frame(image_frame, padding=design.get_spacing('2'))
        info_frame.pack(fill='x', pady=(0, design.get_spacing('3')))
        
        self.image_info_label = tk.Label(info_frame, text="未选择图片", bg=design.get_color('neutral', '50'))
        design.apply_text_style(self.image_info_label, 'body_small')
        self.image_info_label.pack(side='left')
        
        # 图片操作按钮
        btn_frame = ttk.Frame(info_frame)
        btn_frame.pack(side='right')
        
        btn_reload = tk.Button(btn_frame, text="🔄 重新加载", command=self.reload_image)
        design.apply_button_style(btn_reload, 'secondary')
        btn_reload.pack(side='left', padx=design.get_spacing('1'))

        btn_show_explorer = tk.Button(btn_frame, text="📁 显示位置", command=self.show_in_explorer)
        design.apply_button_style(btn_show_explorer, 'secondary')
        btn_show_explorer.pack(side='left', padx=design.get_spacing('1'))
        
        btn_image_info = tk.Button(btn_frame, text="📋 图片信息", command=self.show_image_info)
        design.apply_button_style(btn_image_info, 'secondary')
        btn_image_info.pack(side='left', padx=design.get_spacing('1'))
        
        # 图片显示区域
        self.image_canvas = tk.Canvas(image_frame, bg=design.get_color('neutral', '100'), 
                                        relief='flat', bd=1,
                                        highlightbackground=design.get_color('neutral', '300'),
                                        highlightthickness=1)
        self.image_canvas.pack(fill='both', expand=True, padx=design.get_spacing('4'), pady=design.get_spacing('3'))
        
        # 滚动条
        h_scroll = ttk.Scrollbar(image_frame, orient='horizontal', command=self.image_canvas.xview)
        v_scroll = ttk.Scrollbar(image_frame, orient='vertical', command=self.image_canvas.yview)
        self.image_canvas.configure(xscrollcommand=h_scroll.set, yscrollcommand=v_scroll.set)
        
        h_scroll.pack(side='bottom', fill='x', padx=design.get_spacing('4'))
        v_scroll.pack(side='right', fill='y', pady=design.get_spacing('3'))

        self.image_canvas.bind('<Configure>', self._on_canvas_configure)
        self.image_canvas.bind('<Button-1>', self._on_canvas_click)

    def _on_canvas_configure(self, event):
        """Canvas配置事件处理"""
        if self.current_image_path and (event.width > 0 and event.height > 0):
            if not hasattr(self, '_resize_job_id'):
                self._resize_job_id = None
            
            if self._resize_job_id:
                self.root.after_cancel(self._resize_job_id)
            
            self._resize_job_id = self.root.after(100, lambda: self.display_image(self.current_image_path))
    
    def _on_canvas_click(self, event):
        """Canvas点击事件"""
        # 可以用于实现图像区域选择等功能
        pass
    
    def create_text_results_tab(self):
        """创建文本识别结果标签页"""
        results_frame = ttk.Frame(self.notebook, padding=design.get_spacing('4'))
        self.notebook.add(results_frame, text="📄 识别结果")
        
        # 结果统计框架
        stats_frame = ttk.Frame(results_frame, padding=design.get_spacing('2'))
        stats_frame.pack(fill='x', pady=(0, design.get_spacing('3')))
        
        self.results_stats_label = tk.Label(stats_frame, text="暂无识别结果", bg=design.get_color('neutral', '50'))
        design.apply_text_style(self.results_stats_label, 'body_small')
        self.results_stats_label.pack(side='left')
        
        # 操作按钮
        btn_frame = ttk.Frame(stats_frame)
        btn_frame.pack(side='right')
        
        btn_filter_results = tk.Button(btn_frame, text="🔍 过滤结果", command=self.filter_results_dialog)
        design.apply_button_style(btn_filter_results, 'secondary')
        btn_filter_results.pack(side='left', padx=design.get_spacing('1'))
        
        btn_sort_results = tk.Button(btn_frame, text="📊 排序", command=self.sort_results_dialog)
        design.apply_button_style(btn_sort_results, 'secondary')
        btn_sort_results.pack(side='left', padx=design.get_spacing('1'))
        
        # 文本结果表格
        columns = ('序号', '文本内容', '置信度', '边界框', '行号', '块号', 'CVOCR组件', '布局信息')
        self.results_tree = ttk.Treeview(results_frame, columns=columns, show='headings', height=22)
        
        # 设置列标题和宽度
        column_configs = {
            '序号': (50, 'center'),
            '文本内容': (300, 'w'),
            '置信度': (80, 'center'),
            '边界框': (150, 'center'),
            '行号': (60, 'center'),
            '块号': (60, 'center'),
            'CVOCR组件': (120, 'center'),
            '布局信息': (100, 'center')
        }
        
        for col, (width, anchor) in column_configs.items():
            self.results_tree.heading(col, text=col)
            self.results_tree.column(col, width=width, anchor=anchor)
        
        # 添加滚动条
        tree_scroll = ttk.Scrollbar(results_frame, orient='vertical', command=self.results_tree.yview)
        self.results_tree.configure(yscrollcommand=tree_scroll.set)
        
        # 布局
        self.results_tree.pack(side='left', fill='both', expand=True, padx=(0, design.get_spacing('1')), pady=design.get_spacing('2'))
        tree_scroll.pack(side='right', fill='y', pady=design.get_spacing('2'))
        
        # 绑定双击事件
        self.results_tree.bind('<Double-1>', self.on_text_result_double_click)
        self.results_tree.bind('<Button-3>', self.on_text_result_right_click)  # 右键菜单
    
    def create_text_tab(self):
        """创建纯文本标签页"""
        text_frame = ttk.Frame(self.notebook, padding=design.get_spacing('4'))
        self.notebook.add(text_frame, text="📝 识别报告")
        
        # 文本操作框架
        text_toolbar = ttk.Frame(text_frame, padding=design.get_spacing('2'))
        text_toolbar.pack(fill='x', pady=(0, design.get_spacing('3')))
        
        btn_copy_text = tk.Button(text_toolbar, text="📋 复制文本", command=self.copy_recognized_text)
        design.apply_button_style(btn_copy_text, 'secondary')
        btn_copy_text.pack(side='left', padx=design.get_spacing('1'))

        btn_save_text = tk.Button(text_toolbar, text="💾 保存文本", command=self.save_recognized_text)
        design.apply_button_style(btn_save_text, 'secondary')
        btn_save_text.pack(side='left', padx=design.get_spacing('1'))
        
        btn_search_text = tk.Button(text_toolbar, text="🔍 搜索文本", command=self.search_text_dialog)
        design.apply_button_style(btn_search_text, 'secondary')
        btn_search_text.pack(side='left', padx=design.get_spacing('1'))
        
        btn_text_analysis = tk.Button(text_toolbar, text="📊 文本分析", command=self.analyze_text)
        design.apply_button_style(btn_text_analysis, 'secondary')
        btn_text_analysis.pack(side='left', padx=design.get_spacing('1'))
        
        # 报告显示区域
        self.report_text = scrolledtext.ScrolledText(text_frame, 
                                                    font=design.get_font('base'),
                                                    bg=design.get_color('neutral', '0'),
                                                    fg=design.get_color('neutral', '700'),
                                                    wrap='word', height=30,
                                                    relief='flat', bd=1,
                                                    highlightbackground=design.get_color('neutral', '300'),
                                                    highlightcolor=design.get_color('primary', '600'),
                                                    highlightthickness=1)
        self.report_text.pack(fill='both', expand=True, padx=design.get_spacing('2'), pady=design.get_spacing('2'))
    
    def create_history_tab(self):
        """创建历史记录标签页"""
        history_frame = ttk.Frame(self.notebook, padding=design.get_spacing('4'))
        self.notebook.add(history_frame, text="📚 历史记录")
        
        # 历史记录工具栏
        history_toolbar = ttk.Frame(history_frame, padding=design.get_spacing('2'))
        history_toolbar.pack(fill='x', pady=(0, design.get_spacing('3')))
        
        btn_refresh_history = tk.Button(history_toolbar, text="🔄 刷新", command=self.refresh_history)
        design.apply_button_style(btn_refresh_history, 'secondary')
        btn_refresh_history.pack(side='left', padx=design.get_spacing('1'))

        btn_export_history = tk.Button(history_toolbar, text="📤 导出历史", command=self.export_history)
        design.apply_button_style(btn_export_history, 'secondary')
        btn_export_history.pack(side='left', padx=design.get_spacing('1'))

        btn_clear_history = tk.Button(history_toolbar, text="🧹 清空历史", command=self.clear_history)
        design.apply_button_style(btn_clear_history, 'secondary')
        btn_clear_history.pack(side='left', padx=design.get_spacing('1'))
        
        btn_search_history = tk.Button(history_toolbar, text="🔍 搜索历史", command=self.search_history_dialog)
        design.apply_button_style(btn_search_history, 'secondary')
        btn_search_history.pack(side='left', padx=design.get_spacing('1'))
        
        # 历史记录表格
        columns = ('时间', '图片名称', '文本块数', '字符数', '平均置信度', '使用组件', '状态', '处理时间')
        self.history_tree = ttk.Treeview(history_frame, columns=columns, show='headings')
        
        history_column_configs = {
            '时间': (140, 'center'),
            '图片名称': (200, 'w'),
            '文本块数': (80, 'center'),
            '字符数': (80, 'center'),
            '平均置信度': (100, 'center'),
            '使用组件': (150, 'center'),
            '状态': (80, 'center'),
            '处理时间': (100, 'center')
        }
        
        for col, (width, anchor) in history_column_configs.items():
            self.history_tree.heading(col, text=col)
            self.history_tree.column(col, width=width, anchor=anchor)
        
        # 添加滚动条
        history_scroll = ttk.Scrollbar(history_frame, orient='vertical', command=self.history_tree.yview)
        self.history_tree.configure(yscrollcommand=history_scroll.set)
        
        # 布局
        self.history_tree.pack(side='left', fill='both', expand=True, padx=(0, design.get_spacing('1')), pady=design.get_spacing('2'))
        history_scroll.pack(side='right', fill='y', pady=design.get_spacing('2'))
        
        # 绑定双击事件
        self.history_tree.bind('<Double-1>', self.on_history_double_click)
        self.history_tree.bind('<Button-3>', self.on_history_right_click)
    
    def create_stats_tab(self):
        """创建统计信息标签页"""
        stats_frame = ttk.Frame(self.notebook, padding=design.get_spacing('4'))
        self.notebook.add(stats_frame, text="📈 统计信息")
        
        # 统计控制栏
        stats_toolbar = ttk.Frame(stats_frame, padding=design.get_spacing('2'))
        stats_toolbar.pack(fill='x', pady=(0, design.get_spacing('3')))
        
        btn_refresh_stats = tk.Button(stats_toolbar, text="🔄 刷新统计", command=self.update_enhanced_stats)
        design.apply_button_style(btn_refresh_stats, 'secondary')
        btn_refresh_stats.pack(side='left', padx=design.get_spacing('1'))
        
        btn_export_stats = tk.Button(stats_toolbar, text="📊 导出统计", command=self.export_stats)
        design.apply_button_style(btn_export_stats, 'secondary')
        btn_export_stats.pack(side='left', padx=design.get_spacing('1'))
        
        btn_reset_stats = tk.Button(stats_toolbar, text="🔄 重置统计", command=self.reset_stats)
        design.apply_button_style(btn_reset_stats, 'secondary')
        btn_reset_stats.pack(side='left', padx=design.get_spacing('1'))
        
        # 统计信息显示区域
        self.stats_text = scrolledtext.ScrolledText(stats_frame, 
                                                    font=design.get_font('sm', family='primary'),
                                                    bg=design.get_color('neutral', '0'),
                                                    fg=design.get_color('neutral', '800'),
                                                    relief='flat', bd=1,
                                                    highlightbackground=design.get_color('neutral', '300'),
                                                    highlightthickness=1, wrap='word')
        self.stats_text.pack(fill='both', expand=True, padx=design.get_spacing('2'), pady=design.get_spacing('2'))
        self.stats_text.config(state='disabled')
    
    def create_comparison_tab(self):
        """创建比较分析标签页"""
        comparison_frame = ttk.Frame(self.notebook, padding=design.get_spacing('4'))
        self.notebook.add(comparison_frame, text="🔄 比较分析")
        
        # 比较工具栏
        comparison_toolbar = ttk.Frame(comparison_frame, padding=design.get_spacing('2'))
        comparison_toolbar.pack(fill='x', pady=(0, design.get_spacing('3')))
        
        btn_compare_images = tk.Button(comparison_toolbar, text="🖼️ 比较图片", command=self.compare_images)
        design.apply_button_style(btn_compare_images, 'secondary')
        btn_compare_images.pack(side='left', padx=design.get_spacing('1'))
        
        btn_compare_methods = tk.Button(comparison_toolbar, text="⚖️ 比较方法", command=self.compare_methods)
        design.apply_button_style(btn_compare_methods, 'secondary')
        btn_compare_methods.pack(side='left', padx=design.get_spacing('1'))
        
        # 比较结果显示区域
        self.comparison_text = scrolledtext.ScrolledText(comparison_frame,
                                                        font=design.get_font('base'),
                                                        bg=design.get_color('neutral', '0'),
                                                        fg=design.get_color('neutral', '800'),
                                                        relief='flat', bd=1,
                                                        highlightbackground=design.get_color('neutral', '300'),
                                                        highlightthickness=1, wrap='word')
        self.comparison_text.pack(fill='both', expand=True, padx=design.get_spacing('2'), pady=design.get_spacing('2'))
        self.comparison_text.config(state='disabled')
    
    def create_status_bar(self):
        """创建状态栏"""
        self.status_bar = ttk.Frame(self.root)
        self.status_bar.pack(side='bottom', fill='x', padx=design.get_spacing('2'), pady=design.get_spacing('1'))
        
        # 状态标签
        self.status_text = tk.Label(self.status_bar, text="就绪", bg=design.get_color('neutral', '50'))
        design.apply_text_style(self.status_text, 'caption')
        self.status_text.pack(side='left', padx=design.get_spacing('1'))
        
        # 进度条
        self.progress_bar = ttk.Progressbar(self.status_bar, mode='indeterminate', 
                                            length=200)
        self.progress_bar.pack(side='right', padx=(design.get_spacing('4'), 0))
        
        # 性能指标
        self.performance_label = tk.Label(self.status_bar, text="", bg=design.get_color('neutral', '50'))
        design.apply_text_style(self.performance_label, 'caption')
        self.performance_label.pack(side='right', padx=design.get_spacing('2'))
        
        # 版本信息
        version_label = tk.Label(self.status_bar, text=f"CVOCR v{CVOCRConstants.VERSION}", 
                                bg=design.get_color('neutral', '50'))
        design.apply_text_style(version_label, 'caption')
        version_label.pack(side='right', padx=(0, design.get_spacing('4')))
    
    # 核心功能方法实现
    LOG_MESSAGE = 0
    GUI_TASK = 1 # 保持不变，但现在由 loop.call_soon 调度

    def log_message(self, message: str, level: str = 'INFO'):
        """记录日志消息，并放入队列等待 GUI 线程处理"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        
        icons = {'INFO': 'ℹ️', 'WARNING': '⚠️', 'ERROR': '❌', 'SUCCESS': '✅', 'DEBUG': '🐛'}
        icon = icons.get(level.upper(), 'ℹ️')
        
        formatted_message = f"[{timestamp}] {icon} {message}\n"
        
        if hasattr(self, 'log_queue'): # 确保 GUI 已初始化
            # 使用 put_nowait 避免阻塞日志线程
            try:
                self.log_queue.put_nowait((self.LOG_MESSAGE, formatted_message, message, {}))
            except queue.Full:
                print(f"Log queue is full, dropping message: {formatted_message.strip()}")
        else:
            print(f"GUI未完全初始化，直接打印: {formatted_message.strip()}")

        # 记录到标准logger
        log_level_map = {
            'INFO': logging.INFO,
            'WARNING': logging.WARNING,
            'ERROR': logging.ERROR,
            'CRITICAL': logging.CRITICAL,
            'DEBUG': logging.DEBUG,
            'SUCCESS': logging.INFO
        }
        
        log_module_level = log_level_map.get(level.upper(), logging.INFO)
        logger.log(log_module_level, message)

    async def _process_queues(self):
        """异步处理日志队列和 GUI 任务"""
        while True:
            # 处理日志队列
            while not self.log_queue.empty():
                task_type, formatted_message, status_message, kwargs = self.log_queue.get_nowait()
                if task_type == self.LOG_MESSAGE:
                    # 确保 GUI 更新在 Tkinter 主线程中进行
                    self.root.after(0, self._safe_update_gui_log, formatted_message, status_message)
            
            # 非阻塞等待，让事件循环处理其他协程
            await asyncio.sleep(0.01) # 每隔10ms检查一次队列    

    # --- 修正4: 移除重复的、非异步的 _process_queues 方法 ---
    # (旧的、重复的方法定义已在此处删除)

    def _safe_update_gui_log(self, formatted_message: str, status_message: str):
        """安全更新GUI日志"""
        try:
            self.log_text.config(state='normal')
            self.log_text.insert(tk.END, formatted_message)
            self.log_text.see(tk.END)
            self.log_text.config(state='disabled')
            
            self.status_text.config(text=status_message)
            self.root.update_idletasks()
        except Exception as e:
            print(f"Failed to update GUI log: {e}")
            logger.error(f"Failed to update GUI log: {e}")
    
    def set_processing(self, processing: bool):
        """设置处理状态"""
        self.processing = processing
        if processing:
            self.progress_bar.start()
        else:
            self.progress_bar.stop()
    
    def _load_settings(self):
        """加载设置"""
        try:
            settings_file = 'cvocr_settings.json'
            if os.path.exists(settings_file):
                with open(settings_file, 'r', encoding='utf-8') as f:
                    saved_settings = json.load(f)
                    
                for key, value in saved_settings.items():
                    if key in self.settings:
                        # 特殊处理 CLAHE tile grid size，因为它们是两个变量
                        if key == 'clahe_tile_grid_size_x' or key == 'clahe_tile_grid_size_y':
                            self.settings[key].set(value)
                        # 其他普通变量直接设置
                        else:
                            self.settings[key].set(value)

                # 加载并应用Tesseract路径
                tesseract_path = self.settings['tesseract_path'].get()
                if tesseract_path:
                    success, msg = self.cvocr_manager.set_tesseract_path(tesseract_path)
                    if success:
                        self.log_message(f"✅ 已从配置加载Tesseract路径: {tesseract_path}", 'SUCCESS')
                    else:
                        self.log_message(f"⚠️ 配置文件中的Tesseract路径无效: {tesseract_path}", 'WARNING')
                
                self.log_message("✅ 设置已加载", 'SUCCESS')
        except Exception as e:
            logger.error(f"加载设置失败: {e}\n{traceback.format_exc()}")
    
    def _save_settings(self):
        """保存设置"""
        try:
            settings_file = 'cvocr_settings.json'
            settings_to_save = {}
            
            for key, var in self.settings.items():
                try:
                    settings_to_save[key] = var.get()
                except Exception:
                    pass # 忽略无法获取值的变量
            
            with open(settings_file, 'w', encoding='utf-8') as f:
                json.dump(settings_to_save, f, ensure_ascii=False, indent=2)
            
            self.log_message("💾 设置已保存", 'SUCCESS')
        except Exception as e:
            logger.error(f"保存设置失败: {e}\n{traceback.format_exc()}")
    
    # 核心业务方法实现
    def initialize_cvocr(self):
        """
        初始化CVOCR引擎 (V4.5 - 最终配置同步版)。
        - 全面、安全地从GUI收集所有设置。
        - 将所有设置完整地更新到后端管理器。
        - 使用正确的设置变量启动异步初始化流程。
        """
        # --- 步骤1: 全面、安全地从GUI收集所有设置 ---
        current_gui_config = {}
        for key, var in self.settings.items():
            # 安全地获取值，跳过像 'oem_options' 这样的特殊字典
            if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar)):
                current_gui_config[key] = var.get()
        # 手动添加OEM选项字典
        current_gui_config['oem_options'] = {k: v.get() for k, v in self.settings['oem_options'].items()}
        
        # --- 步骤2: 从收集的配置中提取初始化所需的关键参数 ---
        language_str = current_gui_config.get('language', 'auto')
        language = OCRLanguage(language_str) if language_str != 'auto' else OCRLanguage.AUTO
        
        use_gpu = current_gui_config.get('use_gpu', False)

        # --- 步骤3: 将所有GUI设置完整地同步到后端管理器的配置字典中 ---
        self.cvocr_manager.config.update(current_gui_config)

        # --- 步骤4: 定义并启动异步初始化任务 ---
        async def init_worker_async():
            self.log_message(f"🚀 正在初始化CVOCR引擎 (语言: {language.value}, 精度: 自定义, GPU: {use_gpu})...", 'INFO')
            
            # 为日志构建启用的组件列表
            enabled_components_log = ["Tesseract"] # Tesseract is always a base component
            if self.cvocr_manager.config.get('enable_layout_analysis'): enabled_components_log.append("LayoutLMv2")
            if self.cvocr_manager.config.get('enable_context_analysis'): enabled_components_log.append("GPT-Neo")
            if self.cvocr_manager.config.get('enable_transformer_ocr'): enabled_components_log.append("TransformerOCR")
            if self.settings['enable_advanced_segmentation'].get():
                 enabled_components_log.append("YOLO")
            else:
                 enabled_components_log.append("PP-OCRv3")

            self.log_message(f"🔧 启用组件: {', '.join(enabled_components_log)}", 'INFO')
            
            try:
                # 在后台线程池中运行阻塞的 initialize 方法
                success, message = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    self.cvocr_manager.initialize,
                    language,
                    use_gpu
                )
                # 将结果回调到主线程以更新UI
                self.root.after(0, self._handle_init_result, success, message)
            except Exception as e:
                error_msg = f"CVOCR引擎初始化时发生未捕获的异常: {str(e)}"
                logger.error(error_msg, exc_info=True)
                self.root.after(0, self._handle_init_result, False, error_msg)
            finally:
                # 确保无论成功与否，UI的“处理中”状态都会被重置
                self.root.after(0, self.set_processing, False)

        # 启动UI的“处理中”状态（例如，开始进度条动画）
        self.set_processing(True)
        # 从Tkinter主线程安全地将异步任务调度到后台的asyncio事件循环中
        self.loop.call_soon_threadsafe(self.loop.create_task, init_worker_async())
    
    
    
    def _handle_init_result(self, success: bool, message: str):
        """
        处理初始化结果，并更新GUI的各个相关部分。
        - 更新系统状态区的标签和颜色。
        - 记录详细的初始化日志。
        - 更新新增的TransformerOCR模型加载状态标签。
        - 弹出对话框通知用户初始化结果。
        """
        if success:
            self.status_label.config(text="CVOCR引擎就绪", style='Success.TLabel')
            self.log_message(f"✅ {message}", 'SUCCESS')
            
            # 显示详细的版本和配置信息
            version_info = self.cvocr_manager.version_info
            self.log_message(f"📊 初始化耗时: {version_info.get('init_time', 0):.2f}秒", 'INFO')
            self.log_message(f"🔧 Tesseract版本: {version_info.get('tesseract', 'unknown')}", 'INFO')
            self.log_message(f"🌐 识别语言: {version_info.get('language', 'unknown')}", 'INFO')
            
            # 显示已启用的AI组件状态
            components = version_info.get('components', {})
            if components:
                enabled_components = [comp.replace('_enabled', '').upper() for comp, enabled in components.items() if enabled]
                if enabled_components:
                    self.log_message(f"🎯 已启用组件: {', '.join(enabled_components)}", 'INFO')
            
            # --- 新增：更新TrOCR模型加载状态标签 ---
            # 根据初始化结果中的组件状态来设置标签的文本和颜色。
            if components.get('transformer_ocr_enabled'):
                self.trocr_model_status_label.config(text="✅ 已加载", foreground="green")
            elif self.settings['enable_transformer_ocr'].get():
                # 如果用户勾选了启用，但初始化后组件状态仍为未启用，则说明加载失败
                self.trocr_model_status_label.config(text="❌ 加载失败", foreground="red")
            else:
                # 如果用户未勾选启用，则显示为未启用状态
                self.trocr_model_status_label.config(text=" (未启用)", foreground="gray")

            messagebox.showinfo("初始化成功", f"{message}\n\nCVOCR引擎已就绪，可以开始文本识别！")
        else:
            self.status_label.config(text="初始化失败", style='Error.TLabel')
            self.log_message(f"❌ {message}", 'ERROR')
            
            # --- 新增：在初始化失败时，同样更新TrOCR模型状态标签 ---
            # 如果初始化失败，所有AI模型都应被视为未加载
            self.trocr_model_status_label.config(text="❌ 未加载", foreground="red")
            
            messagebox.showerror("初始化失败", f"{message}\n\n建议先运行系统检查。")

    async def _trigger_initial_system_check_async(self):
        """异步触发初始系统检查"""
        await self.check_system_async()

    def check_system(self):
        """系统检查 (现在调用异步版本)"""
        # 这个同步方法现在只是一个包装器，用于从Tkinter按钮调用
        # 它将实际工作提交给asyncio循环
        if self.loop and self.loop.is_running():
            self.loop.call_soon_threadsafe(self.loop.create_task, self.check_system_async())
        else:
            messagebox.showerror("错误", "Asyncio事件循环未运行，无法执行系统检查。")
            
    async def check_system_async(self):
        """系统检查 (现在是异步协程)"""
        async def check_worker_async():
            self.log_message("🔍 开始CVOCR系统检查...", 'INFO')
            
            try:
                # 阻塞操作放入线程池
                compatible, issues = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor, # 使用 OCR 处理器的线程池
                    CVOCRVersionManager.check_compatibility,
                    self.settings['tesseract_path'].get()
                )
                
                system_info = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    CVOCRVersionManager.get_system_info
                )
                self.log_message(f"💻 系统: {system_info['platform']} {system_info['architecture']}", 'INFO')
                self.log_message(f"🐍 Python: {system_info['python_version']}", 'INFO')
                
                versions = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    CVOCRVersionManager.get_dependency_versions,
                    self.settings['tesseract_path'].get()
                )
                for lib, version in versions.items():
                     self.log_message(f"📦 {lib}: {version}", 'INFO')

                try:
                    memory = await self.loop.run_in_executor(
                        self.async_ocr_processor.executor,
                        psutil.virtual_memory
                    )
                    total_gb = memory.total / (1024**3)
                    available_gb = memory.available / (1024**3)
                    self.log_message(f"💾 系统内存: {total_gb:.1f}GB 总量, {available_gb:.1f}GB 可用", 'INFO')
                    if available_gb < 1:
                        issues.append(f"可用内存较少: {available_gb:.1f}GB，建议至少1GB")
                except ImportError:
                    self.log_message("⚠️ 无法检查内存信息 (psutil未安装)", 'WARNING')
                
                self.root.after(0, self.show_system_issues, issues)
                    
            except Exception as e:
                error_msg = f"系统检查失败: {str(e)}\n{traceback.format_exc()}"
                self.log_message(f"❌ {error_msg}", 'ERROR')
                self.root.after(0, messagebox.showerror, "系统检查失败", f"检查过程中出现错误:\n{str(e)}")
            
            finally:
                self.root.after(0, self.set_processing, False)

        self.set_processing(True)
        # 提交异步任务到 asyncio 事件循环
        await check_worker_async()
    def show_system_issues(self, issues: List[str]):
        """
        显示系统环境问题及解决方案 (增强专业版)
        - 智能分类问题严重性
        - 提供针对性的解决方案和安装命令
        - 集成Tesseract路径修复引导
        """
        if not issues:
            self.status_label.config(text="系统检查通过", style='Success.TLabel')
            self.log_message("✅ 系统检查完成，环境优秀", 'SUCCESS')
            # 系统检查通过后，自动提示初始化
            self._prompt_initialize_cvocr_after_check()
            return

        self.status_label.config(text="系统存在问题", style='Error.TLabel')
        self.log_message(f"⚠️ 系统检查发现 {len(issues)} 个问题，请解决后重试", 'WARNING')

        # --- 问题分类 ---
        critical_issues = []
        optional_issues = []
        tesseract_issue = None

        # 关键阻塞性问题关键词
        critical_keywords = ['Tesseract不可用', 'pytesseract未安装', 'OpenCV未安装', 'Pillow未安装', 'NumPy未安装']
        
        for issue in issues:
            if any(keyword in issue for keyword in critical_keywords):
                if 'Tesseract' in issue:
                    tesseract_issue = issue
                else:
                    critical_issues.append(issue)
            else:
                optional_issues.append(issue)

        # --- Tesseract 专项处理 ---
        if tesseract_issue:
            # 如果是Tesseract问题，优先弹出交互式修复对话框
            if messagebox.askyesno("关键问题：Tesseract OCR 未找到",
                                     f"系统检查发现一个关键问题：\n\n{tesseract_issue}\n\n"
                                     "这是核心OCR引擎，缺少它程序将无法工作。\n"
                                     "这通常是因为Tesseract未安装，或其路径未在系统环境中。\n\n"
                                     "是否需要立即手动选择 `tesseract.exe` 文件来修复此问题？"):
                self._browse_for_tesseract()
                # 引导用户修复后，不再显示通用错误窗口，因为修复后会自动重新检查
                return
        
        # --- 创建详细问题报告窗口 ---
        issue_window = tk.Toplevel(self.root)
        issue_window.title("CVOCR 系统环境报告")
        issue_window.geometry("850x650")
        issue_window.minsize(700, 500)
        issue_window.transient(self.root)
        issue_window.grab_set()
        
        main_frame = ttk.Frame(issue_window, padding=design.get_spacing('6'))
        main_frame.pack(fill='both', expand=True)
        
        # --- 窗口内容 ---
        title_label = tk.Label(main_frame, text="系统环境检查报告", bg=design.get_color('neutral', '50'))
        design.apply_text_style(title_label, 'h2')
        title_label.pack(anchor='w', pady=(0, design.get_spacing('4')))
        
        notebook = ttk.Notebook(main_frame)
        notebook.pack(fill='both', expand=True, pady=design.get_spacing('4'))

        # --- 解决方案标签页 ---
        solution_tab = ttk.Frame(notebook, padding=design.get_spacing('4'))
        notebook.add(solution_tab, text="💡 解决方案")
        
        solution_text = scrolledtext.ScrolledText(solution_tab, wrap='word', height=20, 
                                                                                                    font=design.get_font('body'),
                                                  bg=design.get_color('neutral', '0'),
                                                  fg=design.get_color('neutral', '800'))
        solution_text.pack(fill='both', expand=True)

        solution_content = []
        
        def add_solution(title, description, commands=None):
            solution_content.append(f"📌 {title}\n")
            solution_content.append(f"   {description}\n")
            if commands:
                solution_content.append("   解决方案:\n")
                for cmd_desc, cmd in commands:
                    solution_content.append(f"     • {cmd_desc}:\n       `{cmd}`\n")
            solution_content.append("-" * 60 + "\n")

        # 生成动态解决方案
        if tesseract_issue:
            add_solution("Tesseract OCR 引擎不可用 (关键)",
                         "这是执行OCR的核心组件，必须安装并配置。",
                         [("Windows (推荐)", "访问 https://github.com/UB-Mannheim/tesseract/wiki 下载并安装"),
                          ("macOS (使用Homebrew)", "brew install tesseract tesseract-lang"),
                          ("Ubuntu/Debian", "sudo apt update && sudo apt install tesseract-ocr tesseract-ocr-chi-sim tesseract-ocr-eng")])
        
        for issue in critical_issues:
            if 'pytesseract' in issue:
                add_solution("Python Tesseract 接口未安装 (关键)",
                             "缺少连接Python与Tesseract引擎的桥梁。",
                             [("安装命令", "pip install pytesseract")])
            elif 'OpenCV' in issue:
                add_solution("OpenCV 库未安装 (关键)",
                             "核心图像处理库，用于读取、操作和显示图像。",
                             [("安装命令", "pip install opencv-python")])
            elif 'Pillow' in issue:
                add_solution("Pillow (PIL) 库未安装 (关键)",
                             "基础图像处理库，用于与Tkinter交互。",
                             [("安装命令", "pip install Pillow")])
            elif 'NumPy' in issue:
                add_solution("NumPy 库未安装 (关键)",
                             "Python科学计算的基础库，图像处理依赖它。",
                             [("安装命令", "pip install numpy")])

        if optional_issues:
            solution_content.append("\n=== 可选功能依赖问题 ===\n")
            solution_content.append("以下问题不影响核心OCR功能，但会使高级AI增强特性不可用。\n\n")

            for issue in optional_issues:
                if 'Transformers' in issue:
                    add_solution("Transformers 库未安装 (可选)",
                                 "用于LayoutLMv2布局分析和GPT-Neo上下文纠错。",
                                 [("安装命令", "pip install transformers")])
                elif 'PyTorch' in issue:
                    add_solution("PyTorch 深度学习框架未安装 (可选)",
                                 "Transformers库依赖此框架运行。",
                                 [("CPU版本 (推荐)", "pip install torch torchvision torchaudio"),
                                  ("NVIDIA GPU版本 (CUDA 11.8)", "pip install torch torchvision torchaudio --index-url https://download.pytorch.org/whl/cu118")])
                elif '版本过低' in issue:
                    lib_name = issue.split('版本过低')[0].strip()
                    add_solution(f"{lib_name} 版本过低 (建议升级)",
                                 f"当前版本可能存在兼容性问题或缺少必要功能。",
                                 [("升级命令", f"pip install --upgrade {lib_name.lower()}")])
                elif '可用内存较少' in issue: # 添加psutil检测到的内存问题解决方案
                    add_solution("可用内存不足 (建议)",
                                 "系统可用内存可能不足以运行所有高级OCR模型，可能导致性能下降或崩溃。",
                                 [("建议", "关闭不必要的应用程序，或考虑升级系统内存。")])


        solution_text.insert(1.0, "".join(solution_content))
        solution_text.config(state='disabled')

        # --- 完整问题列表标签页 ---
        issues_tab = ttk.Frame(notebook, padding=design.get_spacing('4'))
        notebook.add(issues_tab, text=f"📋 问题列表 ({len(issues)})")
        
        issues_list_text = scrolledtext.ScrolledText(issues_tab, wrap='word', height=20,
                                                     font=design.get_font('body'),
                                                     bg=design.get_color('neutral', '0'),
                                                     fg=design.get_color('neutral', '800'))
        issues_list_text.pack(fill='both', expand=True)
        
        full_issues_content = "检测到的所有环境问题：\n\n"
        for i, issue in enumerate(issues, 1):
            full_issues_content += f"{i}. {issue}\n"
        issues_list_text.insert(1.0, full_issues_content)
        issues_list_text.config(state='disabled')

        # --- 底部按钮区域 ---
        btn_frame = ttk.Frame(main_frame)
        btn_frame.pack(fill='x', pady=(design.get_spacing('4'), 0))

        def copy_solutions_to_clipboard():
            try:
                self.root.clipboard_clear()
                self.root.clipboard_append(solution_text.get(1.0, tk.END))
                self.log_message("📋 解决方案已复制到剪贴板", 'SUCCESS')
            except Exception as e:
                messagebox.showerror("复制失败", f"无法复制内容: {e}")

        btn_copy = tk.Button(btn_frame, text="📋 复制解决方案", command=copy_solutions_to_clipboard)
        design.apply_button_style(btn_copy, 'secondary')
        btn_copy.pack(side='left')

        btn_retry = tk.Button(btn_frame, text="🔄 重新检查", 
                              command=lambda: (issue_window.destroy(), self.check_system()))
        design.apply_button_style(btn_retry, 'primary')
        btn_retry.pack(side='right')
        
        btn_close_issue = tk.Button(btn_frame, text="关闭", command=issue_window.destroy)
        design.apply_button_style(btn_close_issue, 'secondary')
        btn_close_issue.pack(side='right', padx=design.get_spacing('2'))

    def _browse_for_tesseract(self):
        """打开文件对话框让用户选择tesseract.exe"""
        self.log_message("🔍 正在等待用户选择 Tesseract.exe...", 'INFO')
        
        filetypes = [("Tesseract 可执行文件", "tesseract.exe"), ("所有文件", "*.*")] if sys.platform == "win32" else [("所有文件", "*.*")]
        
        tesseract_path = filedialog.askopenfilename(
            title="请选择 tesseract.exe 文件",
            filetypes=filetypes
        )
        
        if tesseract_path:
            success, msg = self.cvocr_manager.set_tesseract_path(tesseract_path)
            if success:
                self.settings['tesseract_path'].set(tesseract_path)
                self._save_settings()  # 保存设置以便下次使用
                self.log_message(f"✅ Tesseract路径已成功设置并保存。", 'SUCCESS')
                messagebox.showinfo("设置成功",
                                    f"Tesseract 路径已成功设置为:\n{tesseract_path}\n\n"
                                    "设置已保存。正在重新检查系统状态...")
                # 重新进行系统检查以确认
                self.check_system()
            else:
                self.log_message(f"❌ 设置Tesseract路径失败: {msg}", 'ERROR')
                messagebox.showerror("设置失败", f"设置Tesseract路径失败: {msg}")
    
    def _prompt_initialize_cvocr_after_check(self):
        """系统检查后提示初始化CVOCR"""
        if self.cvocr_manager.is_initialized:
            return

        if messagebox.askyesno("CVOCR引擎初始化", 
                                "系统检查完成。是否立即初始化CVOCR引擎？\n"
                                "首次初始化可能需要下载语言包，请确保网络畅通。"):
            self.initialize_cvocr()
    
    def select_image(self):
        """
        选择图片文件，并进行验证。
        (V4.3 - 缓存清除版): 选择新图片时，会自动清除上一张图片的预处理缓存，
        以确保后续预览功能（如分割预览）使用的是当前图片的最新预处理结果。
        """
        file_path = filedialog.askopenfilename(
            title="选择图片文件",
            filetypes=[
                ("所有支持的图片", "*.jpg *.jpeg *.png *.bmp *.tiff *.tif *.webp *.gif"),
                ("JPEG文件", "*.jpg *.jpeg"),
                ("PNG文件", "*.png"),
                ("BMP文件", "*.bmp"),
                ("TIFF文件", "*.tiff *.tif"),
                ("WebP文件", "*.webp"),
                ("GIF文件", "*.gif"),
                ("所有文件", "*.*")
            ]
        )
        
        if file_path:
            # 使用增强的图像验证方法
            valid, message = AdvancedTextImageProcessor.validate_image(file_path)
            if not valid:
                self.log_message(f"❌ 图片验证失败: {message}", 'ERROR')
                messagebox.showerror("图片无效", f"选择的文件无效:\n{message}")
                return
            
            self.current_image_path = file_path
            
            # --- 关键修正：清除旧的预处理缓存 ---
            self._cached_preprocessed_image = None
            self.log_message("新图片已选择，预处理缓存已清除。", "DEBUG")
            # --- 修正结束 ---

            self.display_image(file_path)
            
            # 获取并显示详细的图片信息
            try:
                with Image.open(file_path) as img:
                    width, height = img.size
                    mode = img.mode
                    file_size = os.path.getsize(file_path) / 1024
                    
                    info_text = f"文件: {os.path.basename(file_path)} | 尺寸: {width}x{height} | 模式: {mode} | 大小: {file_size:.1f}KB"
                    self.image_info_label.config(text=info_text)

                self.log_message(f"✅ 已选择图片: {os.path.basename(file_path)}", 'SUCCESS')
            except Exception as e:
                self.log_message(f"❌ 读取图片信息失败: {e}", 'ERROR')


    def select_batch_images(self):
        """选择多个图片文件进行批量处理"""
        file_paths = filedialog.askopenfilenames(
            title="选择多个图片文件",
            filetypes=[
                ("所有支持的图片", "*.jpg *.jpeg *.png *.bmp *.tiff *.tif *.webp *.gif"),
                ("JPEG文件", "*.jpg *.jpeg"),
                ("PNG文件", "*.png"),
                ("BMP文件", "*.bmp"),
                ("TIFF文件", "*.tiff *.tif"),
                ("WebP文件", "*.webp"),
                ("GIF文件", "*.gif"),
                ("所有文件", "*.*")
            ]
        )

        if file_paths:
            # 验证所有图片
            valid_files = []
            for path in file_paths:
                valid, message = AdvancedTextImageProcessor.validate_image(path)
                if valid:
                    valid_files.append(path)
                else:
                    self.log_message(f"⚠️ 批量选择中跳过无效图片 '{os.path.basename(path)}': {message}", 'WARNING')
            
            if not valid_files:
                messagebox.showwarning("无有效图片", "所选文件中没有有效的图片可用于批量处理。")
                self.log_message("❌ 批量处理：没有选择到任何有效图片。", 'ERROR')
                return

            self.batch_image_paths = valid_files
            self.log_message(f"✅ 已选择 {len(valid_files)} 张图片进行批量处理。", 'SUCCESS')
            self.settings['batch_processing'].set(True) # 自动切换到批量处理模式
            
            # 尝试在图像预览区显示第一张图片
            if self.batch_image_paths:
                self.current_image_path = self.batch_image_paths[0]
                self.display_image(self.current_image_path)
                self.image_info_label.config(text=f"批量处理模式 | 已加载 {len(self.batch_image_paths)} 张图片")
            self.notebook.select(self.notebook.index("end") - 1) # 切换到历史记录或统计页
            self.notebook.select(self.notebook.index("end") - 2) # 切换到历史记录或统计页
            messagebox.showinfo("批量处理", f"已选择 {len(valid_files)} 张图片，点击 '批量处理' 按钮开始。")

    def display_image(self, image_path: str, text_blocks: Optional[List[Dict]] = None, shape_blocks: Optional[List[Dict]] = None):
        """
        在Canvas上显示图像，并根据需要精确绘制文本和图形的边界框。
        - 保持图像的原始纵横比进行缩放。
        - 将缩放后的图像在画布中居中显示。
        - 存储坐标转换参数，以便后续功能（如高亮）使用。
        - 为文本和图形绘制不同样式的边界框。

        Args:
            image_path (str): 要显示的图像文件的完整路径。
            text_blocks (Optional[List[Dict]]): 包含已识别文本块及其边界框的列表。
            shape_blocks (Optional[List[Dict]]): 包含已检测图形及其边界框的列表。
        """
        try:
            # 1. 验证文件路径
            if not os.path.exists(image_path):
                self.log_message(f"❌ 图像文件不存在: {image_path}", 'ERROR')
                self.image_canvas.delete("all")
                return

            # 2. 加载原始图像并清空画布
            original_img = Image.open(image_path)
            self.image_canvas.delete("all")

            # 3. 存储关键的原始尺寸信息
            self._last_original_image_size = original_img.size
            img_width, img_height = self._last_original_image_size

            # 4. 获取画布尺寸
            canvas_width = self.image_canvas.winfo_width()
            canvas_height = self.image_canvas.winfo_height()

            # 如果画布尚未渲染（尺寸为0或1），则中止绘制以避免错误
            if canvas_width <= 1 or canvas_height <= 1:
                return

            # 5. 计算缩放比例和偏移量以保持纵横比并居中
            # 分别计算水平和垂直方向的缩放比例
            scale_ratio_x = canvas_width / img_width
            scale_ratio_y = canvas_height / img_height

            # 选择较小的比例作为最终的统一缩放因子，以确保整个图像都能被容纳
            final_scale_ratio = min(scale_ratio_x, scale_ratio_y)

            # 计算缩放后的显示尺寸
            display_width = int(img_width * final_scale_ratio)
            display_height = int(img_height * final_scale_ratio)
            
            # 计算为了在画布中居中而产生的左上角偏移量
            x_offset = (canvas_width - display_width) // 2
            y_offset = (canvas_height - display_height) // 2
            
            # 6. 存储这些转换参数，以便后续功能（如高亮、点击等）可以复用
            self._last_display_scale_ratio_x = final_scale_ratio
            self._last_display_scale_ratio_y = final_scale_ratio
            self._last_display_x_offset = x_offset
            self._last_display_y_offset = y_offset

            # 7. 缩放图像并显示
            # 使用LANCZOS（抗锯齿）算法以获得最佳的图像缩小质量
            resized_img = original_img.resize((display_width, display_height), Image.Resampling.LANCZOS)
            self.photo = ImageTk.PhotoImage(resized_img)
            self.image_canvas.create_image(x_offset, y_offset, image=self.photo, anchor='nw', tags="image")
            
            # 8. 绘制文本块的边界框（红色）
            if text_blocks:
                for block in text_blocks:
                    bbox = block.get('bbox')
                    # 确保bbox存在且格式正确
                    if not bbox or len(bbox) != 4:
                        continue
                    
                    # 获取原始坐标
                    x1_orig, y1_orig, x2_orig, y2_orig = bbox
                    
                    # 应用缩放和偏移，计算出在Canvas上的最终坐标
                    x1_canvas = int(x1_orig * self._last_display_scale_ratio_x + x_offset)
                    y1_canvas = int(y1_orig * self._last_display_scale_ratio_y + y_offset)
                    x2_canvas = int(x2_orig * self._last_display_scale_ratio_x + x_offset)
                    y2_canvas = int(y2_orig * self._last_display_scale_ratio_y + y_offset)
                    
                    # 绘制与图像上文字完美对齐的矩形框
                    self.image_canvas.create_rectangle(
                        x1_canvas, y1_canvas, x2_canvas, y2_canvas, 
                        outline='red', width=2, tags=("bbox", "text_bbox")
                    )

            # 9. 绘制图形的边界框（绿色，更粗）
            if shape_blocks:
                for block in shape_blocks:
                    bbox = block.get('bbox')
                    if not bbox or len(bbox) != 4:
                        continue
                    
                    x1_orig, y1_orig, x2_orig, y2_orig = bbox
                    
                    x1_canvas = int(x1_orig * self._last_display_scale_ratio_x + x_offset)
                    y1_canvas = int(y1_orig * self._last_display_scale_ratio_y + y_offset)
                    x2_canvas = int(x2_orig * self._last_display_scale_ratio_x + x_offset)
                    y2_canvas = int(y2_orig * self._last_display_scale_ratio_y + y_offset)

                    self.image_canvas.create_rectangle(
                        x1_canvas, y1_canvas, x2_canvas, y2_canvas, 
                        outline='green', width=3, tags=("bbox", "shape_bbox")
                    )

            # 10. 更新画布的滚动区域以包含所有绘制的内容
            self.image_canvas.config(scrollregion=self.image_canvas.bbox("all"))

            # 强制Tkinter立即更新界面
            self.root.update_idletasks()

        except Exception as e:
            # 捕获所有可能的异常，如文件损坏、内存不足等
            self.log_message(f"❌ 显示图像或绘制边界框时失败: {e}", 'ERROR')
            # 打印完整的堆栈跟踪以方便调试
            traceback.print_exc()
    
    
    def reload_image(self):
        """重新加载当前图片"""
        if self.current_image_path:
            self.display_image(self.current_image_path)
            self.log_message(f"✅ 已重新加载图片: {os.path.basename(self.current_image_path)}", 'SUCCESS')
        else:
            self.log_message("⚠️ 没有图片可供重新加载。", 'WARNING')

    def show_in_explorer(self):
        """在文件浏览器中显示当前图片"""
        if self.current_image_path and os.path.exists(self.current_image_path):
            try:
                if platform.system() == "Windows":
                    os.startfile(os.path.dirname(self.current_image_path))
                elif platform.system() == "Darwin":  # macOS
                    subprocess.Popen(["open", os.path.dirname(self.current_image_path)])
                else:  # Linux
                    subprocess.Popen(["xdg-open", os.path.dirname(self.current_image_path)])
                self.log_message(f"📁 已在文件浏览器中打开: {os.path.dirname(self.current_image_path)}", 'INFO')
            except Exception as e:
                self.log_message(f"❌ 无法打开文件浏览器: {e}", 'ERROR')
                messagebox.showerror("错误", f"无法在文件浏览器中打开路径:\n{e}")
        else:
            self.log_message("⚠️ 没有图片路径或文件不存在。", 'WARNING')

    def show_image_info(self):
        """显示当前图片详细信息"""
        if not self.current_image_path or not os.path.exists(self.current_image_path):
            messagebox.showinfo("图片信息", "未选择图片或图片文件不存在。")
            return

        try:
            with Image.open(self.current_image_path) as img:
                width, height = img.size
                mode = img.mode
                file_size_bytes = os.path.getsize(self.current_image_path)
                file_size_mb = file_size_bytes / (1024 * 1024)
                file_ext = os.path.splitext(self.current_image_path)[1].lower()
                
                info_content = (
                    f"文件名: {os.path.basename(self.current_image_path)}\n"
                    f"完整路径: {self.current_image_path}\n"
                    f"图片尺寸: {width} x {height} 像素\n"
                    f"颜色模式: {mode}\n"
                    f"文件大小: {file_size_mb:.2f} MB ({file_size_bytes} 字节)\n"
                    f"文件类型: {file_ext.upper()}\n"
                    f"修改时间: {datetime.fromtimestamp(os.path.getmtime(self.current_image_path)).strftime('%Y-%m-%d %H:%M:%S')}\n"
                )
                
                # 添加预处理器的质量评估信息
                _, _, metadata = self.image_processor.intelligent_preprocess_image(
                    self.current_image_path, enable_preprocessing=True # 强制评估
                )
                if metadata and 'quality_metrics' in metadata:
                    info_content += "\n--- 图像质量评估 ---\n"
                    quality_metrics = metadata['quality_metrics']
                    for key, value in quality_metrics.items():
                        info_content += f"{key.replace('_', ' ').title()}: {value:.2f}\n"
                    info_content += f"质量等级: {metadata.get('quality_level', 'N/A')}\n"
                    info_content += f"总质量分数: {metadata.get('quality_score', 0):.2f}\n"

                messagebox.showinfo("图片详细信息", info_content)
                self.log_message(f"📋 已显示图片 '{os.path.basename(self.current_image_path)}' 的详细信息。", 'INFO')

        except Exception as e:
            self.log_message(f"❌ 获取图片详细信息失败: {e}", 'ERROR')
            messagebox.showerror("错误", f"获取图片详细信息失败:\n{e}")
    def _get_enabled_segmentation_algorithms(self) -> List[str]:
        """收集所有当前启用的高级分割算法名称"""
        enabled_algos = []
        for key, var in self.settings.items():
            if key.startswith('seg_') and var.get():
                # 将 'seg_improved_mser' 转换为 'improved_mser'
                algo_name = key.replace('seg_', '')
                enabled_algos.append(algo_name)
        return enabled_algos
    def start_enhanced_recognition(self):
        """
        开始增强文本识别 (V4.2 - GUI参数完全同步最终版)。
        此方法作为用户点击“开始识别”按钮的入口，负责：
        1. 执行所有前置检查（如处理状态、引擎初始化、图片选择）。
        2. 全面收集GUI界面上所有相关的设置，包括所有预处理开关和高级分割技术选项。
        3. 将这些设置更新到后端的 CVOCRManager 实例中。
        4. 创建并调度一个异步的识别任务，以避免阻塞GUI。
        """
        # --- 步骤 1: 执行所有前置检查 ---
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行识别或批量处理，请稍候。")
            return
        
        if not self.cvocr_manager.is_initialized:
            if messagebox.askyesno("CVOCR引擎未初始化", "CVOCR引擎尚未初始化。是否立即初始化？"):
                self.initialize_cvocr()
            else:
                self.log_message("❌ 识别操作取消：CVOCR引擎未初始化。", 'ERROR')
                return

        if not self.current_image_path:
            messagebox.showwarning("未选择图片", "请先选择一张图片。")
            self.log_message("❌ 识别操作取消：未选择图片。", 'ERROR')
            return
        
        if not os.path.exists(self.current_image_path):
            messagebox.showerror("图片不存在", f"图片文件 '{self.current_image_path}' 不存在。")
            self.log_message("❌ 识别操作取消：图片文件不存在。", 'ERROR')
            return

        # --- 步骤 2: 设置处理状态并记录日志 ---
        self.set_processing(True)
        self.log_message(f"🚀 开始识别图片: {os.path.basename(self.current_image_path)}", 'INFO')
        
        # --- 步骤 3: 全面收集GUI设置并更新后端管理器 ---
        language_str = self.settings['language'].get()
        language = OCRLanguage(language_str) if language_str != 'auto' else OCRLanguage.AUTO
        enable_preprocessing = self.settings['enable_preprocessing'].get()
        use_gpu = self.settings['use_gpu'].get()

        self.cvocr_manager.config.update({
            # OCR核心参数
            'language': language.value,
            'psm': self.settings['psm_mode'].get(),
            'confidence_threshold': self.settings['confidence_threshold'].get(),
            'oem_options': {k: v.get() for k, v in self.settings['oem_options'].items()},
            
            # 预处理主开关
            'enable_preprocessing_optimization': enable_preprocessing,
            
            # 详细预处理参数
            'enable_deskew': self.settings['enable_deskew'].get(),
            'deskew_angle_threshold': self.settings['deskew_angle_threshold'].get(),
            'remove_borders': self.settings['remove_borders'].get(),
            'border_threshold': self.settings['border_threshold'].get(),
            'crop_to_content': self.settings['crop_to_content'].get(),
            'page_border_detection': self.settings['page_border_detection'].get(),
            'shadow_removal': self.settings['shadow_removal'].get(),
            'bilateral_filter': self.settings['bilateral_filter'].get(),
            'bilateral_d': self.settings['bilateral_d'].get(),
            'bilateral_sigma_color': self.settings['bilateral_sigma_color'].get(),
            'bilateral_sigma_space': self.settings['bilateral_sigma_space'].get(),
            'histogram_equalization': self.settings['histogram_equalization'].get(),
            'apply_clahe': self.settings['apply_clahe'].get(),
            'clahe_clip_limit': self.settings['clahe_clip_limit'].get(),
            'clahe_tile_grid_size': (self.settings['clahe_tile_grid_size_x'].get(), self.settings['clahe_tile_grid_size_y'].get()),
            'unsharp_mask': self.settings['unsharp_mask'].get(),
            'unsharp_radius': self.settings['unsharp_radius'].get(),
            'unsharp_amount': self.settings['unsharp_amount'].get(),
            'adaptive_block_size': self.settings['adaptive_block_size'].get(),
            'adaptive_c_constant': self.settings['adaptive_c_constant'].get(),
            'enable_grayscale': self.settings['enable_grayscale'].get(),
            'enable_binarization': self.settings['enable_binarization'].get(),
            
            # AI组件开关
            'enable_layout_analysis': self.settings['enable_layout_analysis'].get(),
            'enable_context_analysis': self.settings['enable_context_analysis'].get(),
            'enable_transformer_ocr': self.settings['enable_transformer_ocr'].get(),
            
            # 性能与高级模型参数
            'use_gpu': use_gpu,
            'transformer_ocr_model': self.settings['transformer_ocr_model'].get(),
            
            # 高级分割/全元素检测参数
            'enable_advanced_segmentation': self.settings['enable_advanced_segmentation'].get(),
            'segmentation_recognizer': self.settings['segmentation_recognizer'].get(),
            'enable_tesseract_fine_tuning': self.settings['enable_tesseract_fine_tuning'].get(),
            'enabled_segmentation_algorithms': self._get_enabled_segmentation_algorithms(),
            'enable_smart_line_merge': self.settings['enable_smart_line_merge'].get(),
        })
        
        # --- 步骤 4: 创建并调度异步识别任务 ---
        async def recognition_worker_async(image_path_to_process, enable_preproc, lang):
            try:
                # 在执行前，确保manager内部的language是最新的
                self.cvocr_manager.language = lang
                
                # 更新Tesseract配置以匹配最新的语言和PSM设置
                init_tess_success, init_tess_msg = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    self.cvocr_manager._initialize_tesseract
                )
                if not init_tess_success:
                    self.log_message(f"❌ Tesseract引擎配置更新失败: {init_tess_msg}", 'ERROR')
                    self.root.after(0, self.set_processing, False)
                    self.root.after(0, messagebox.showerror, "识别失败", f"Tesseract引擎配置更新失败: {init_tess_msg}")
                    return

                # 调用核心识别方法，它将使用manager中已更新的config
                results, message = await self.async_ocr_processor.run_blocking_ocr_task(
                    image_path_to_process,
                    enable_preproc
                )
                
                # 将结果回调到主线程处理GUI更新
                self.root.after(0, self._handle_recognition_result, image_path_to_process, results, message)
            except Exception as e:
                error_msg = f"识别图片 '{os.path.basename(image_path_to_process)}' 失败: {str(e)}\n{traceback.format_exc()}"
                self.root.after(0, self._handle_recognition_result, image_path_to_process, None, error_msg)
            finally:
                # 确保无论成功失败，处理状态都会被重置
                self.root.after(0, self.set_processing, False)
                self.root.after(0, self._update_performance_display)

        # 将异步任务提交到事件循环中执行
        self.loop.call_soon_threadsafe(self.loop.create_task, recognition_worker_async(
            self.current_image_path, 
            enable_preprocessing, 
            language
        ))
    
    
    def preview_preprocessing(self):
        """
        预览当前图像应用所有预处理设置后的效果。
        此版本修复了因引用已移除的 'enable_advanced_preprocessing' 设置而导致的 KeyError。
        """
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行其他操作，请稍候。")
            return
            
        if not self.current_image_path:
            messagebox.showwarning("未选择图片", "请先选择一张图片以预览其预处理效果。")
            return

        self.set_processing(True)
        self.log_message(f"🔬 正在生成预处理预览: {os.path.basename(self.current_image_path)}", 'INFO')

        # 收集所有相关的预处理设置
        # --- 核心修正：移除了对不存在的 'enable_advanced_preprocessing' 的引用 ---
        preprocess_options = {
            'enable_preprocessing': True, # 预览时强制启用
            'enable_advanced_segmentation': False, # 模拟纯文本识别流程以展示所有效果
            # 'force_intensive_preprocessing' 键已移除
            'enable_deskew': self.settings['enable_deskew'].get(),
            'deskew_angle_threshold': self.settings['deskew_angle_threshold'].get(),
            'remove_borders': self.settings['remove_borders'].get(),
            'border_threshold': self.settings['border_threshold'].get(),
            'crop_to_content': self.settings['crop_to_content'].get(),
            'page_border_detection': self.settings['page_border_detection'].get(),
            'shadow_removal': self.settings['shadow_removal'].get(),
            # 'denoise_strength' 和 'edge_preservation' 在当前 image_processor 中未直接使用，但保留以备将来扩展
            # 'denoise_strength': self.settings['denoise_strength'].get(),
            # 'edge_preservation': self.settings['edge_preservation'].get(),
            'unsharp_mask': self.settings['unsharp_mask'].get(),
            'unsharp_radius': self.settings['unsharp_radius'].get(),
            'unsharp_amount': self.settings['unsharp_amount'].get(),
            'histogram_equalization': self.settings['histogram_equalization'].get(),
            'bilateral_filter': self.settings['bilateral_filter'].get(),
            'bilateral_d': self.settings['bilateral_d'].get(),
            'bilateral_sigma_color': self.settings['bilateral_sigma_color'].get(),
            'bilateral_sigma_space': self.settings['bilateral_sigma_space'].get(),
            'apply_clahe': self.settings['apply_clahe'].get(),
            'clahe_clip_limit': self.settings['clahe_clip_limit'].get(),
            'clahe_tile_grid_size': (self.settings['clahe_tile_grid_size_x'].get(), self.settings['clahe_tile_grid_size_y'].get()),
            'adaptive_block_size': self.settings['adaptive_block_size'].get(),
            'adaptive_c_constant': self.settings['adaptive_c_constant'].get(),
            'enable_grayscale': self.settings['enable_grayscale'].get(),
            'enable_binarization': self.settings['enable_binarization'].get(),
        }

        async def preview_worker_async():
            try:
                # 在后台线程中运行阻塞的图像处理任务
                task_to_run = functools.partial(
                    self.image_processor.intelligent_preprocess_image,
                    self.current_image_path,
                    **preprocess_options
                )
                
                processed_image_np, msg, metadata = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    task_to_run
                )
                
                # 将结果回调到主线程以显示预览窗口
                if processed_image_np is not None:
                    original_image = Image.open(self.current_image_path)
                    processed_image_pil = Image.fromarray(cv2.cvtColor(processed_image_np, cv2.COLOR_BGR2RGB))
                    self.root.after(0, self._show_preprocessing_preview_window, original_image, processed_image_pil, metadata)
                else:
                    self.log_message(f"❌ 预处理预览生成失败: {msg}", 'ERROR')
                    self.root.after(0, messagebox.showerror, "预览失败", f"生成预处理预览失败:\n{msg}")

            except Exception as e:
                error_msg = f"生成预处理预览时发生错误: {e}\n{traceback.format_exc()}"
                self.log_message(f"❌ {error_msg}", 'ERROR')
                self.root.after(0, messagebox.showerror, "预览失败", error_msg)
            finally:
                self.root.after(0, self.set_processing, False)
        
        # 将异步任务提交到事件循环中
        self.loop.call_soon_threadsafe(self.loop.create_task, preview_worker_async())
    
    
    
    
    def preview_segmentation(self):
        """
        启动一个异步任务，以预览当前图像应用用户自定义的文本分割（切割）技术后的效果。
        (V4.5 - 最终调用修正版)
        """
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行其他操作，请稍候。")
            return
            
        if not self.current_image_path:
            messagebox.showwarning("未选择图片", "请先选择一张图片以预览其分割效果。")
            return
            
        if not self.cvocr_manager.is_initialized or not self.cvocr_manager.text_detector:
            messagebox.showerror("引擎未就绪", "CVOCR引擎或文本检测器未初始化，无法进行分割预览。")
            return

        self.set_processing(True)
        self.log_message(f"📊 正在生成分割预览: {os.path.basename(self.current_image_path)}", 'INFO')

        async def preview_worker_async():
            try:
                processed_image_np = None

                if self._cached_preprocessed_image is not None:
                    self.log_message("   - 步骤1: 检测到已缓存的预处理图像，直接使用。", 'INFO')
                    processed_image_np = self._cached_preprocessed_image
                else:
                    self.log_message("   - 步骤1: 未找到缓存，正在实时应用图像预处理...", 'WARNING')
                    preprocess_options = { key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar)) }
                    preprocess_options['enable_preprocessing'] = True

                    task_preprocess = functools.partial(
                        self.image_processor.intelligent_preprocess_image,
                        self.current_image_path,
                        **preprocess_options
                    )
                    processed_image_np, _, _ = await self.loop.run_in_executor(
                        self.async_ocr_processor.executor, task_preprocess
                    )

                if processed_image_np is None:
                    raise Exception("图像预处理失败，无法继续进行分割。")
                
                self.log_message(f"   - 步骤2: 使用用户自定义技术组合进行文本检测...", 'INFO')
                
                enabled_algorithms = self._get_enabled_segmentation_algorithms()
                if not enabled_algorithms:
                     raise Exception("没有选择任何分割技术。请在'高级文本分割技术'区域勾选至少一项。")
                
                if len(processed_image_np.shape) == 2:
                    image_for_detection = cv2.cvtColor(processed_image_np, cv2.COLOR_GRAY2BGR)
                else:
                    image_for_detection = processed_image_np

                # --- 核心修正：采用“先更新配置，再调用”的统一模式 ---
                
                # 1. 收集并更新检测器的内部配置
                current_config = {key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar))}
                self.cvocr_manager.text_detector.config.update(current_config)
                
                # 2. 准备不带 precision_level 参数的调用
                task_detect = functools.partial(
                    self.cvocr_manager.text_detector.detect_text_regions_advanced,
                    image_for_detection,
                    enabled_algorithms
                )
                regions, metadata = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor, task_detect
                )
                
                self.log_message(f"   - 步骤3: 检测到 {len(regions)} 个文本区域，正在生成可视化...", 'INFO')
                
                task_draw = functools.partial(
                    self._draw_segmentation_on_image,
                    self.current_image_path,
                    regions,
                    processed_image_np
                )
                original_pil, processed_pil_with_boxes = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor, task_draw
                )

                self.root.after(0, self._show_segmentation_preview_window, original_pil, processed_pil_with_boxes, metadata)

            except Exception as e:
                error_msg = f"生成分割预览时发生错误: {e}"
                logger.error(f"{error_msg}\n{traceback.format_exc()}", exc_info=True)
                self.log_message(f"❌ {error_msg}", 'ERROR')
                self.root.after(0, messagebox.showerror, "预览失败", error_msg)
            finally:
                self.root.after(0, self.set_processing, False)

        self.loop.call_soon_threadsafe(self.loop.create_task, preview_worker_async())
    
    def _draw_segmentation_on_image(self, image_path: str, regions: List[np.ndarray], processed_image_np: np.ndarray) -> Tuple[Image.Image, Image.Image]:
        """
        加载原始图像，并在预处理后的图像副本上绘制分割区域。
        这是一个辅助方法，设计为在后台线程中运行。

        Args:
            image_path (str): 原始图像的文件路径，用于在预览窗口左侧显示。
            regions (List[np.ndarray]): 检测到的文本区域（分割框）列表。
            processed_image_np (np.ndarray): 经过预处理后的图像NumPy数组，将在此图像上绘制分割框。

        Returns:
            Tuple[Image.Image, Image.Image]: 一个包含两个PIL图像的元组：
                                             1. 原始图像。
                                             2. 带有分割框的预处理后图像。
        """
        # 加载原始图像用于左侧显示
        original_image_np = cv2.imread(image_path)
        original_pil = Image.fromarray(cv2.cvtColor(original_image_np, cv2.COLOR_BGR2RGB))
        
        # 使用传入的、已预处理的图像作为绘制的画布
        # 首先确保它是RGB格式以便PIL处理
        if len(processed_image_np.shape) == 2: # 如果是灰度图
            image_with_regions = cv2.cvtColor(processed_image_np, cv2.COLOR_GRAY2RGB)
        else: # 如果是BGR图
            image_with_regions = cv2.cvtColor(processed_image_np, cv2.COLOR_BGR2RGB)
        
        # 绘制所有检测到的多边形区域
        if regions:
            # 将所有区域点转换为适用于 polylines 的整数坐标格式
            pts = [np.array(region, np.int32) for region in regions]
            # 在图像上绘制所有多边形，颜色为亮绿色，线宽为2像素
            cv2.polylines(image_with_regions, pts, isClosed=True, color=(0, 255, 0), thickness=2)
            
        # 将绘制后的 NumPy 数组转为 PIL 图像，用于在预览窗口右侧显示
        segmented_pil = Image.fromarray(image_with_regions)
        
        return original_pil, segmented_pil

    def _show_segmentation_preview_window(self, original_img: Image.Image, segmented_processed_img: Image.Image, metadata: Dict):
        """
        创建一个新窗口来并排显示原始图像和带有分割结果的预处理后图像。
        (V4.3 - 工作流修正版): 
        - 左侧显示原始图，用于基准对比。
        - 右侧显示在预处理后的图像上绘制的分割框，直观展示预处理+分割的联合效果。
        - 底部显示本次操作所使用的具体分割算法组合。
        """
        preview_window = tk.Toplevel(self.root)
        preview_window.title("文本分割（切割）效果预览")
        preview_window.geometry("1600x800")
        preview_window.transient(self.root)
        preview_window.grab_set()

        main_frame = ttk.Frame(preview_window, padding=design.get_spacing('4'))
        main_frame.pack(fill='both', expand=True)

        # 图像显示区
        image_frame = ttk.Frame(main_frame)
        image_frame.pack(fill='both', expand=True)

        # 左侧：原始图像
        original_frame = ttk.LabelFrame(image_frame, text="原始图像", padding=design.get_spacing('2'))
        original_frame.pack(side='left', fill='both', expand=True, padx=(0, design.get_spacing('2')))
        original_canvas = tk.Canvas(original_frame, bg=design.get_color('neutral', '100'))
        original_canvas.pack(fill='both', expand=True)

        # 右侧：预处理 + 分割结果
        segmented_frame = ttk.LabelFrame(image_frame, text="预处理 + 分割结果 (绿色框)", padding=design.get_spacing('2'))
        segmented_frame.pack(side='right', fill='both', expand=True, padx=(design.get_spacing('2'), 0))
        segmented_canvas = tk.Canvas(segmented_frame, bg=design.get_color('neutral', '100'))
        segmented_canvas.pack(fill='both', expand=True)

        # 底部信息区
        info_frame = ttk.LabelFrame(main_frame, text="检测信息", padding=design.get_spacing('3'))
        info_frame.pack(fill='x', pady=(design.get_spacing('4'), 0))

        # 显示元数据
        total_regions = metadata.get('total_regions', 0)
        proc_time = metadata.get('processing_time', 0.0)
        # 从元数据中获取实际使用的算法列表
        algorithms_used = ", ".join(metadata.get('algorithms_used', ['N/A']))
        
        info_text = f"使用算法: {algorithms_used} | 检测到区域数: {total_regions} | 耗时: {proc_time:.3f} 秒"
        info_label = tk.Label(info_frame, text=info_text, justify='left', bg=design.get_color('neutral', '50'))
        design.apply_text_style(info_label, 'body')
        info_label.pack(anchor='w')

        # 动态调整图片大小以适应Canvas的函数
        def resize_and_display(canvas: tk.Canvas, img: Image.Image):
            canvas.update_idletasks()
            canvas_w, canvas_h = canvas.winfo_width(), canvas.winfo_height()
            if canvas_w <= 1 or canvas_h <= 1: return
            
            img_w, img_h = img.size
            scale = min(canvas_w / img_w, canvas_h / img_h)
            new_w, new_h = int(img_w * scale), int(img_h * scale)
            
            resized = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(resized)
            
            # 存储引用防止被垃圾回收
            canvas.image = photo
            
            x_offset = (canvas_w - new_w) // 2
            y_offset = (canvas_h - new_h) // 2
            canvas.create_image(x_offset, y_offset, image=photo, anchor='nw')

        # 延迟绑定resize事件，确保窗口已创建
        preview_window.after(100, lambda: [
            resize_and_display(original_canvas, original_img),
            resize_and_display(segmented_canvas, segmented_processed_img),
            original_canvas.bind('<Configure>', lambda e: resize_and_display(original_canvas, original_img)),
            segmented_canvas.bind('<Configure>', lambda e: resize_and_display(segmented_canvas, segmented_processed_img))
        ])

        self.log_message("✅ 成功生成分割预览窗口。", 'SUCCESS')


    def _show_preprocessing_preview_window(self, original_img: Image.Image, processed_img: Image.Image, metadata: Dict):
        """
        创建一个新窗口来并排显示原始图像和预处理后的图像。
        (V4.3 - 缓存结果版): 此版本在显示预览的同时，会将处理后的图像缓存到实例变量中，
        以供“预览分割结果”功能直接使用，实现工作流的无缝衔接。
        """
        preview_window = tk.Toplevel(self.root)
        preview_window.title("图像预处理效果预览")
        preview_window.geometry("1600x800")
        preview_window.transient(self.root)
        preview_window.grab_set()

        main_frame = ttk.Frame(preview_window, padding=design.get_spacing('4'))
        main_frame.pack(fill='both', expand=True)

        # 图像显示区
        image_frame = ttk.Frame(main_frame)
        image_frame.pack(fill='both', expand=True)

        # 原始图像
        original_frame = ttk.LabelFrame(image_frame, text="原始图像", padding=design.get_spacing('2'))
        original_frame.pack(side='left', fill='both', expand=True, padx=(0, design.get_spacing('2')))
        original_canvas = tk.Canvas(original_frame, bg=design.get_color('neutral', '100'))
        original_canvas.pack(fill='both', expand=True)

        # 预处理后图像
        processed_frame = ttk.LabelFrame(image_frame, text="预处理后", padding=design.get_spacing('2'))
        processed_frame.pack(side='right', fill='both', expand=True, padx=(design.get_spacing('2'), 0))
        processed_canvas = tk.Canvas(processed_frame, bg=design.get_color('neutral', '100'))
        processed_canvas.pack(fill='both', expand=True)

        # 底部信息区
        info_frame = ttk.LabelFrame(main_frame, text="处理信息", padding=design.get_spacing('3'))
        info_frame.pack(fill='x', pady=(design.get_spacing('4'), 0))

        # 显示处理步骤
        operations = metadata.get('operations', ['无操作'])
        operations_text = " -> ".join(operations)
        info_label = tk.Label(info_frame, text=f"处理流程: {operations_text}", 
                              wraplength=1500, justify='left', bg=design.get_color('neutral', '50'))
        design.apply_text_style(info_label, 'body_small')
        info_label.pack(anchor='w')

        # 动态调整图片大小以适应Canvas
        def resize_and_display(canvas: tk.Canvas, img: Image.Image):
            canvas.update_idletasks() # 确保获取到正确的canvas尺寸
            canvas_w, canvas_h = canvas.winfo_width(), canvas.winfo_height()
            if canvas_w <= 1 or canvas_h <= 1: return
            
            img_w, img_h = img.size
            scale = min(canvas_w / img_w, canvas_h / img_h)
            new_w, new_h = int(img_w * scale), int(img_h * scale)
            
            resized = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(resized)
            
            # 存储引用防止被垃圾回收
            canvas.image = photo 
            
            # 在Canvas中央显示图片
            x_offset = (canvas_w - new_w) // 2
            y_offset = (canvas_h - new_h) // 2
            canvas.create_image(x_offset, y_offset, image=photo, anchor='nw')

        # 延迟绑定resize事件，确保窗口已创建
        preview_window.after(100, lambda: [
            resize_and_display(original_canvas, original_img),
            resize_and_display(processed_canvas, processed_img),
            original_canvas.bind('<Configure>', lambda e: resize_and_display(original_canvas, original_img)),
            processed_canvas.bind('<Configure>', lambda e: resize_and_display(processed_canvas, processed_img))
        ])

        # 将处理后的图像（PIL.Image）转换为NumPy数组（BGR格式）并缓存
        # 这是实现“预处理 -> 分割预览”工作流衔接的关键步骤
        self._cached_preprocessed_image = cv2.cvtColor(np.array(processed_img), cv2.COLOR_RGB2BGR)
        self.log_message("✅ 成功生成预处理预览窗口，并已缓存处理结果。", 'SUCCESS')
    
    
    def _handle_recognition_result(self, image_path: str, results: Optional[Dict], message: str):
        """
        处理识别结果，并全面更新GUI的各个部分。
        """
        try:
            if results is None or results.get('error'):
                self.log_message(f"❌ 识别失败: {message}", 'ERROR')
                messagebox.showerror("识别失败", f"识别图片 '{os.path.basename(image_path)}' 失败:\n{message}")
                
                self.report_text.config(state='normal')
                self.report_text.delete(1.0, tk.END)
                self.report_text.insert(tk.END, f"识别失败: {message}")
                self.report_text.config(state='disabled')
                
                self.results_tree.delete(*self.results_tree.get_children())
                self.results_stats_label.config(text="识别失败")

                fail_results_entry = {
                    'full_text': '', 'text_blocks': [], 'error': message,
                    'total_blocks': 0, 'total_characters': 0, 'average_confidence': 0,
                    'language': self.settings['language'].get(),
                    'cvocr_components': self.cvocr_manager.config.get('components', {}),
                    'processing_metadata': {'total_processing_time': 0, 'error': message}
                }
                self.result_manager.add_result(image_path, fail_results_entry, fail_results_entry.get('processing_metadata'))
                return

            self.log_message(f"✅ 识别成功: {message}", 'SUCCESS')
            
            entry = self.result_manager.add_result(image_path, results, results.get('processing_metadata'))
            if entry and self.settings['auto_save_results'].get():
                try:
                    base_name = os.path.splitext(os.path.basename(image_path))[0]
                    save_dir = "ocr_results"
                    os.makedirs(save_dir, exist_ok=True)
                    output_file = os.path.join(save_dir, f"{base_name}_result.json")
                    with open(output_file, 'w', encoding='utf-8') as f:
                        json.dump(entry, f, ensure_ascii=False, indent=2)
                    self.log_message(f"💾 识别结果已自动保存到: {output_file}", 'INFO')
                except Exception as e:
                    self.log_message(f"❌ 自动保存结果失败: {e}", 'ERROR')

            self.report_text.config(state='normal')
            self.report_text.delete(1.0, tk.END)
            self.report_text.insert(tk.END, results.get('full_text', ''))
            self.report_text.config(state='disabled')

            self.results_tree.delete(*self.results_tree.get_children())
            all_blocks = results.get('text_blocks', [])
            
            for i, block in enumerate(all_blocks):
                confidence_str = f"{block.get('confidence', 0):.1f}%"
                bbox = block.get('bbox', [0,0,0,0])
                bbox_str = f"({bbox[0]},{bbox[1]},{bbox[2]},{bbox[3]})"
                
                if block.get('is_shape', False):
                    components_str = "图形检测"
                    text_display = block.get('text', '')
                    layout_info_str = 'N/A'
                else:
                    text_display = block.get('text', '')[:50] + "..." if len(block.get('text', '')) > 50 else block.get('text', '')
                    components_from_entry = entry.get('cvocr_components', {}) 
                    used_components = [k.replace('_used', '') for k, v in components_from_entry.items() if v]
                    components_str = "+".join(used_components) if used_components else 'Tesseract'
                    layout_info_str = block.get('layout_info', {}).get('region_type', 'N/A')
                
                self.results_tree.insert('', 'end', values=(
                    i + 1, text_display, confidence_str, bbox_str,
                    block.get('line_num', 0), block.get('block_num', 0),
                    components_str, layout_info_str
                ), iid=f"block_{i}")

            total_char_count = results.get('total_characters', 0)
            avg_confidence_display = results.get('average_confidence', 0)
            self.results_stats_label.config(text=f"总元素块: {len(all_blocks)} | 总字符: {total_char_count} | 平均置信度: {avg_confidence_display:.1f}%")

            text_blocks_to_draw = [b for b in all_blocks if not b.get('is_shape', False)]
            shape_blocks_to_draw = [b for b in all_blocks if b.get('is_shape', False)]
            self.display_image(image_path, text_blocks=text_blocks_to_draw, shape_blocks=shape_blocks_to_draw)
            
            self.refresh_history()
            self.update_enhanced_stats()

            self.notebook.select(1)
            self.root.update_idletasks()

        except Exception as e:
            error_msg = f"处理识别结果并更新GUI时发生致命错误: {str(e)}\n{traceback.format_exc()}"
            self.log_message(f"❌ {error_msg}", 'ERROR')
            messagebox.showerror("GUI更新失败", error_msg)
        finally:
            self.set_processing(False)
            self._update_performance_display()
    
    
    def batch_process(self):
        """批量处理多个图片文件 (现在是异步协程)"""
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行识别或批量处理，请稍候。")
            return

        if not self.cvocr_manager.is_initialized:
            if messagebox.askyesno("CVOCR引擎未初始化", "CVOCR引擎尚未初始化。是否立即初始化？"):
                self.initialize_cvocr()
            else:
                self.log_message("❌ 批量处理取消：CVOCR引擎未初始化。", 'ERROR')
                return

        if not hasattr(self, 'batch_image_paths') or not self.batch_image_paths:
            messagebox.showwarning("无图片可批量处理", "请先点击 '批量选择' 按钮选择要批量处理的图片。")
            self.log_message("❌ 批量处理取消：未选择批量图片。", 'ERROR')
            return

        self.set_processing(True)
        self.log_message(f"⚡ 开始批量识别 {len(self.batch_image_paths)} 张图片...", 'INFO')

       
        language_str = self.settings['language'].get()
        language = OCRLanguage(language_str) if language_str != 'auto' else OCRLanguage.AUTO
        enable_preprocessing = self.settings['enable_preprocessing'].get()
        use_gpu = self.settings['use_gpu'].get()

        self.cvocr_manager.config.update({
            'language': language.value,
            'enable_preprocessing_optimization': enable_preprocessing,
            'use_gpu': use_gpu,
            'enable_deskew': self.settings['enable_deskew'].get(),
            'deskew_angle_threshold': self.settings['deskew_angle_threshold'].get(),
            'remove_borders': self.settings['remove_borders'].get(),
            'border_threshold': self.settings['border_threshold'].get(),
            'crop_to_content': self.settings['crop_to_content'].get(),
            'page_border_detection': self.settings['page_border_detection'].get(),
            'shadow_removal': self.settings['shadow_removal'].get(),
            'unsharp_mask': self.settings['unsharp_mask'].get(),
            'unsharp_radius': self.settings['unsharp_radius'].get(),
            'unsharp_amount': self.settings['unsharp_amount'].get(),
            'histogram_equalization': self.settings['histogram_equalization'].get(),
            'bilateral_filter': self.settings['bilateral_filter'].get(),
            'bilateral_d': self.settings['bilateral_d'].get(),
            'bilateral_sigma_color': self.settings['bilateral_sigma_color'].get(),
            'bilateral_sigma_space': self.settings['bilateral_sigma_space'].get(),
            'apply_clahe': self.settings['apply_clahe'].get(),
            'clahe_clip_limit': self.settings['clahe_clip_limit'].get(),
            'clahe_tile_grid_size': (self.settings['clahe_tile_grid_size_x'].get(), self.settings['clahe_tile_grid_size_y'].get()),
            'adaptive_block_size': self.settings['adaptive_block_size'].get(),
            'adaptive_c_constant': self.settings['adaptive_c_constant'].get(),
            'psm': self.settings['psm_mode'].get(),
            'confidence_threshold': self.settings['confidence_threshold'].get(),
            'enable_layout_analysis': self.settings['enable_layout_analysis'].get(),
            'enable_context_analysis': self.settings['enable_context_analysis'].get(),
            'enable_transformer_ocr': self.settings['enable_transformer_ocr'].get(),
        })

        self.cvocr_manager.language = language
        
        async def batch_process_async():
            init_tess_success, init_tess_msg = await self.loop.run_in_executor(
                self.async_ocr_processor.executor,
                self.cvocr_manager._initialize_tesseract
            )
            if not init_tess_success:
                self.log_message(f"❌ 批量处理取消：Tesseract引擎配置更新失败: {init_tess_msg}", 'ERROR')
                self.root.after(0, self.set_processing, False)
                self.root.after(0, messagebox.showerror, "批量处理失败", f"Tesseract引擎配置更新失败: {init_tess_msg}")
                return

            tasks = []
            for i, image_path_to_process in enumerate(self.batch_image_paths):
                task = self.async_ocr_processor.run_blocking_ocr_task(
                    image_path_to_process,
                    enable_preprocessing
                )
                tasks.append(task)
            
            completed_count = 0
            total_count = len(tasks)
            # 使用 enumerate 来同时获取索引和 future 对象
            for i, future in enumerate(asyncio.as_completed(tasks)):
                completed_count += 1
                # 从原始列表中获取对应的图片路径
                image_path_for_result = self.batch_image_paths[i]
                try:
                    results, message = await future
                    self.root.after(0, self._handle_batch_result, image_path_for_result, results, message, completed_count, total_count)
                except Exception as e:
                    error_msg = f"批量识别图片 '{os.path.basename(image_path_for_result)}' 失败: {str(e)}\n{traceback.format_exc()}"
                    self.log_message(f"❌ [{completed_count}/{total_count}] {error_msg}", 'ERROR')
                    self.root.after(0, self._handle_batch_result, image_path_for_result, None, error_msg, completed_count, total_count)

            self.log_message(f"✅ 批量处理完成！共处理 {total_count} 张图片。", 'SUCCESS')
            self.root.after(0, self.set_processing, False)
            self.root.after(0, self._update_performance_display)

        self.loop.call_soon_threadsafe(self.loop.create_task, batch_process_async())
    
    def _handle_batch_result(self, image_path: str, results: Optional[Dict], message: str, completed_count: int, total_count: int):
        """处理批量识别中的单个结果，更新GUI和历史记录"""
        progress_msg = f"⚡ [{completed_count}/{total_count}]"
        if results is None or results.get('error'):
            self.log_message(f"{progress_msg} 识别失败图片 '{os.path.basename(image_path)}': {message}", 'ERROR')
            # 仍然添加到历史记录，但标记为失败
            fail_results = {
                'full_text': '', 'text_blocks': [], 'error': message,
                'total_blocks': 0, 'total_characters': 0, 'average_confidence': 0,
                'language': self.settings['language'].get(),
                'cvocr_components': self.cvocr_manager.config.get('components', {}),
                'processing_metadata': {'total_processing_time': 0, 'error': message}
            }
            self.result_manager.add_result(image_path, fail_results, fail_results.get('processing_metadata'))
        else:
            self.log_message(f"{progress_msg} 识别成功图片 '{os.path.basename(image_path)}': {message}", 'SUCCESS')
            self.result_manager.add_result(image_path, results, results.get('processing_metadata'))
        
        # 刷新历史记录和统计信息，但可能不需要每次都更新详细结果和图片预览
        self.refresh_history()
        self.update_enhanced_stats()
        self.notebook.select(3) # 切换到历史记录标签页

    def quick_ocr(self):
        """快速OCR，直接识别当前图片 (现在是异步协程)"""
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行识别，请稍候。")
            return
        if not self.cvocr_manager.is_initialized:
            if messagebox.askyesno("CVOCR引擎未初始化", "CVOCR引擎尚未初始化。是否立即初始化？"):
                self.initialize_cvocr()
            else:
                self.log_message("❌ 快速OCR取消：CVOCR引擎未初始化。", 'ERROR')
                return
        if not self.current_image_path:
            messagebox.showwarning("未选择图片", "请先选择一张图片。")
            self.log_message("❌ 快速OCR取消：未选择图片。", 'ERROR')
            return
        
        self.log_message(f"⚡ 开始快速OCR识别图片: {os.path.basename(self.current_image_path)}", 'INFO')
        self.set_processing(True)

        language_str = self.settings['language'].get()
        language = OCRLanguage(language_str) if language_str != 'auto' else OCRLanguage.AUTO
        
        # 【最终强化】: 创建一个干净、独立的配置字典用于快速OCR，确保不受任何其他设置的干扰。
        quick_config = {
            'language': language.value,
            'psm': 3,  # 使用PSM 3进行整页自动分割，最符合快速端到端识别的逻辑。
            'oem': 3,  # 使用默认的LSTM引擎。
            'confidence_threshold': 0, # 在快速模式下，我们希望看到所有结果，不过滤。
            'use_gpu': self.settings['use_gpu'].get(),
            'quick_mode': True, # <--- 新增：添加一个明确的“快速模式”标记

            # --- 显式禁用所有高级功能 ---
            'enable_preprocessing': False, # 禁用所有在AdvancedTextImageProcessor中的复杂预处理。
            'enable_preprocessing_optimization': False, # 确保manager也知道预处理已禁用。
            'enable_advanced_segmentation': False, # 强制关闭全元素检测/高级分割模式。
            'enable_layout_analysis': False,
            'enable_context_analysis': False,
            'enable_transformer_ocr': False,
            'enable_smart_line_merge': False,
            'enable_layoutlm_merge': False,
        }

        # 将这个干净的配置应用到管理器
        self.cvocr_manager.config.update(quick_config)
        self.cvocr_manager.language = language
        
        async def quick_ocr_worker_async(image_path_to_process, lang):
            try:
                # 重新初始化Tesseract配置，以确保使用PSM 3
                init_tess_success, init_tess_msg = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    self.cvocr_manager._initialize_tesseract
                )
                if not init_tess_success:
                    self.log_message(f"❌ 快速OCR取消：Tesseract引擎配置更新失败: {init_tess_msg}", 'ERROR')
                    self.root.after(0, self.set_processing, False)
                    self.root.after(0, messagebox.showerror, "快速OCR失败", f"Tesseract引擎配置更新失败: {init_tess_msg}")
                    return

                # 调用核心识别函数，第二个参数 `enable_preprocessing` 为 False
                results, message = await self.async_ocr_processor.run_blocking_ocr_task(
                    image_path_to_process,
                    False 
                )
                self.root.after(0, self._handle_recognition_result, image_path_to_process, results, message)
            except Exception as e:
                error_msg = f"快速OCR图片 '{os.path.basename(image_path_to_process)}' 失败: {str(e)}\n{traceback.format_exc()}"
                self.root.after(0, self._handle_recognition_result, image_path_to_process, None, error_msg)
            finally:
                self.root.after(0, self.set_processing, False)
                self.root.after(0, self._update_performance_display)

        self.loop.call_soon_threadsafe(self.loop.create_task, quick_ocr_worker_async(self.current_image_path, language))
    
    
    def show_visualization(self):
        """显示当前识别结果的边界框可视化"""
        if not self.result_manager.current_results:
            messagebox.showwarning("无结果", "请先执行OCR识别操作以获取结果。")
            return
        
        results = self.result_manager.current_results
        # Use the image path from the current result in result_manager
        current_result_entry = self.result_manager.get_result_by_id(self.result_manager.history[0]['id']) if self.result_manager.history else None
        image_path = current_result_entry['image_path'] if current_result_entry else None

        if not image_path:
            messagebox.showwarning("无图片", "无法找到对应的原始图片。")
            return

        bboxes = []
        for block in results.get('text_blocks', []):
            bboxes.append(block['bbox'])
        
        self.display_image(image_path, bboxes=bboxes)
        self.log_message(f"📊 已在图片预览中显示边界框。", 'INFO')

    def export_current_results(self):
        """导出当前识别结果"""
        if not self.result_manager.current_results:
            messagebox.showwarning("无结果", "没有可导出的当前识别结果。")
            return
        
        # 允许用户选择导出格式
        file_options = [
            ("JSON文件", "*.json"),
            ("文本文件", "*.txt"),
            ("所有文件", "*.*")
        ]
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=file_options,
            title="保存识别结果"
        )
        
        if file_path:
            try:
                extension = os.path.splitext(file_path)[1].lower()
                results_to_export = self.result_manager.current_results
                
                if extension == ".json":
                    with open(file_path, 'w', encoding='utf-8') as f:
                        json.dump(results_to_export, f, ensure_ascii=False, indent=2)
                elif extension == ".txt":
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(results_to_export.get('full_text', ''))
                else:
                    messagebox.showwarning("不支持的格式", "请选择JSON或TXT格式进行导出。")
                    self.log_message(f"❌ 导出结果失败：不支持的文件格式 {extension}。", 'ERROR')
                    return

                self.log_message(f"📤 当前识别结果已导出到: {file_path}", 'SUCCESS')
                messagebox.showinfo("导出成功", f"识别结果已成功导出到:\n{file_path}")
            except Exception as e:
                self.log_message(f"❌ 导出当前识别结果失败: {e}", 'ERROR')
                messagebox.showerror("导出失败", f"导出识别结果失败:\n{e}")

    def clear_results(self):
        """清空当前显示的识别结果和图片上的边界框"""
        self.report_text.config(state='normal')
        self.report_text.delete(1.0, tk.END)
        self.report_text.config(state='disabled')
        
        self.results_tree.delete(*self.results_tree.get_children())
        self.results_stats_label.config(text="暂无识别结果")
        
        self.image_canvas.delete("bbox") # 清除所有tag为"bbox"的元素
        self.image_canvas.delete("highlight_bbox") # 清除高亮边框
        self.current_bboxes = []
        self.log_message("🧹 当前识别结果已清空。", 'INFO')

    def compare_results(self):
        """打开一个新窗口以比较两个历史识别结果"""
        # 这是一个复杂的功能，需要单独的UI来选择两个历史结果并进行比较
        # 暂时只弹出一个提示框，实际功能待实现
        messagebox.showinfo("功能待实现", "比较结果功能正在开发中，敬请期待！")
        self.log_message("ℹ️ 比较结果功能正在开发中。", 'INFO')

    def copy_recognized_text(self):
        """复制识别到的纯文本到剪贴板"""
        text = self.report_text.get(1.0, tk.END).strip()
        if text:
            try:
                self.root.clipboard_clear()
                self.root.clipboard_append(text)
                self.log_message("📋 识别文本已复制到剪贴板。", 'SUCCESS')
            except Exception as e:
                self.log_message(f"❌ 复制文本到剪贴板失败: {e}", 'ERROR')
                messagebox.showerror("复制失败", f"无法复制文本到剪贴板:\n{e}")
        else:
            messagebox.showwarning("无文本", "没有可复制的识别文本。")

    def save_recognized_text(self):
        """保存识别到的纯文本到文件"""
        text = self.report_text.get(1.0, tk.END).strip()
        if not text:
            messagebox.showwarning("无文本", "没有可保存的识别文本。")
            return
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")],
            title="保存识别文本"
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(text)
                self.log_message(f"💾 识别文本已保存到: {file_path}", 'SUCCESS')
                messagebox.showinfo("保存成功", f"识别文本已成功保存到:\n{file_path}")
            except Exception as e:
                self.log_message(f"❌ 保存识别文本失败: {e}", 'ERROR')
                messagebox.showerror("保存失败", f"保存识别文本失败:\n{e}")

    def search_text_dialog(self):
        """在当前报告文本中搜索"""
        search_window = tk.Toplevel(self.root)
        search_window.title("搜索文本")
        search_window.geometry("400x150")
        search_window.transient(self.root)
        search_window.grab_set()

        search_frame = ttk.Frame(search_window, padding=design.get_spacing('4'))
        search_frame.pack(fill='both', expand=True)

        tk.Label(search_frame, text="搜索内容:", bg=design.get_color('neutral', '50')).pack(anchor='w', pady=(0, design.get_spacing('1')))
        search_entry = ttk.Entry(search_frame, width=40)
        search_entry.pack(fill='x', pady=(0, design.get_spacing('2')))
        search_entry.focus_set()

        def perform_search():
            query = search_entry.get()
            if not query:
                return

            text_content = self.report_text.get(1.0, tk.END)
            start_index = "1.0"
            count = tk.IntVar()
            
            self.report_text.tag_remove("search_highlight", "1.0", tk.END) # 清除旧高亮
            
            while True:
                start_index = self.report_text.search(query, start_index, stopindex=tk.END, count=count, nocase=True)
                if not start_index:
                    break
                end_index = self.report_text.index(f"{start_index}+{len(query)}c")
                self.report_text.tag_add("search_highlight", start_index, end_index)
                start_index = end_index
            
            self.report_text.tag_config("search_highlight", background="yellow", foreground="black")
            
            if count.get() > 0:
                self.log_message(f"🔍 在报告中找到 '{query}' {count.get()} 次。", 'INFO')
                messagebox.showinfo("搜索结果", f"找到 '{query}' {count.get()} 次。")
            else:
                self.log_message(f"🔍 在报告中未找到 '{query}'。", 'INFO')
                messagebox.showinfo("搜索结果", f"未找到 '{query}'。")

            search_window.destroy()

        search_button = tk.Button(search_frame, text="搜索", command=perform_search)
        design.apply_button_style(search_button, 'primary')
        search_button.pack(pady=(design.get_spacing('2'), 0))

        search_entry.bind("<Return>", lambda event: perform_search())

    def analyze_text(self):
        """对当前识别报告进行文本分析"""
        full_text = self.report_text.get(1.0, tk.END).strip()
        if not full_text:
            messagebox.showwarning("无文本", "没有可分析的文本。")
            return

        analysis_report = []
        analysis_report.append("--- 文本分析报告 ---\n")
        
        # 字符数 (包括空格)
        char_count = len(full_text)
        analysis_report.append(f"总字符数 (含空格): {char_count}\n")

        # 字符数 (不含空格)
        char_count_no_spaces = len(full_text.replace(" ", "").replace("\n", "").replace("\t", ""))
        analysis_report.append(f"总字符数 (不含空格): {char_count_no_spaces}\n")
        
        # 词汇数
        words = full_text.split()
        word_count = len(words)
        analysis_report.append(f"总词汇数: {word_count}\n")
        
        # 平均词长
        if word_count > 0:
            avg_word_length = sum(len(word) for word in words) / word_count
            analysis_report.append(f"平均词长: {avg_word_length:.2f}\n")
        
        # 唯一词汇数
        unique_words = set(w.lower() for w in words)
        unique_word_count = len(unique_words)
        analysis_report.append(f"唯一词汇数: {unique_word_count}\n")

        # 行数
        line_count = full_text.count('\n') + 1 # 假设至少有一行
        analysis_report.append(f"总行数: {line_count}\n")

        # 最常见词汇
        if word_count > 0:
            from collections import Counter
            word_frequencies = Counter(w.lower() for w in words)
            most_common_words = word_frequencies.most_common(5)
            analysis_report.append("\n最常见词汇 (前5):\n")
            for word, freq in most_common_words:
                analysis_report.append(f"  - {word}: {freq} 次\n")

        # 语言分布 (如果结果中包含)
        if self.result_manager.current_results and 'language' in self.result_manager.current_results:
            analysis_report.append(f"\n检测语言: {self.result_manager.current_results['language']}\n")
        
        # 总体置信度 (如果结果中包含)
        if self.result_manager.current_results and 'average_confidence' in self.result_manager.current_results:
            analysis_report.append(f"平均置信度: {self.result_manager.current_results['average_confidence']:.2f}%\n")
        
        analysis_report.append(f"\n报告生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

        # 在新窗口中显示报告
        analysis_window = tk.Toplevel(self.root)
        analysis_window.title("文本分析报告")
        analysis_window.geometry("600x500")
        analysis_window.transient(self.root)
        analysis_window.grab_set()

        analysis_text_area = scrolledtext.ScrolledText(analysis_window, wrap='word', 
                                                       font=design.get_font('body'),
                                                       bg=design.get_color('neutral', '0'),
                                                       fg=design.get_color('neutral', '800'))
        analysis_text_area.pack(fill='both', expand=True, padx=design.get_spacing('2'), pady=design.get_spacing('2'))
        analysis_text_area.insert(tk.END, "".join(analysis_report))
        analysis_text_area.config(state='disabled')
        
        self.log_message("📊 已生成文本分析报告。", 'INFO')

    def refresh_history(self):
        """刷新历史记录列表"""
        self.history_tree.delete(*self.history_tree.get_children())
        history_entries = self.result_manager.get_history()
        
        for i, entry in enumerate(history_entries):
            components = entry.get('cvocr_components', {})
            used_components_str = "+".join([k.replace('_used', '') for k, v in components.items() if v]) if components else "Tesseract"
            
            status = "成功" 
            if 'error' in entry.get('results', {}):
                status = "错误"
            elif entry.get('total_blocks', 0) == 0 and entry.get('full_text', '') == '':
                status = "无文本" # Differentiate from a processing 'error'

            self.history_tree.insert('', 'end', values=(
                datetime.fromisoformat(entry['timestamp']).strftime('%Y-%m-%d %H:%M:%S'),
                entry['image_name'],
                entry.get('total_blocks', 0),
                entry.get('total_characters', 0),
                f"{entry.get('avg_confidence', 0):.1f}%",
                used_components_str,
                status,
                f"{entry.get('processing_time', 0):.2f}s"
            ), iid=entry['id'])
        
        self.log_message(f"📚 历史记录已刷新，共 {len(history_entries)} 条记录。", 'INFO')

    def export_history(self):
        """导出所有历史记录"""
        if not self.result_manager.history:
            messagebox.showwarning("无历史记录", "没有可导出的历史记录。")
            return
        
        file_options = [
            ("JSON文件", "*.json"),
            ("CSV文件", "*.csv"),
            ("所有文件", "*.*")
        ]
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=file_options,
            title="导出历史记录"
        )
        
        if file_path:
            try:
                extension = os.path.splitext(file_path)[1].lower()
                success, msg = self.result_manager.export_history(file_path, export_format=extension.lstrip('.'))
                if success:
                    self.log_message(f"📤 历史记录已导出到: {file_path}", 'SUCCESS')
                    messagebox.showinfo("导出成功", f"历史记录已成功导出到:\n{file_path}")
                else:
                    self.log_message(f"❌ 导出历史记录失败: {msg}", 'ERROR')
                    messagebox.showerror("导出失败", f"导出历史记录失败:\n{msg}")
            except Exception as e:
                self.log_message(f"❌ 导出历史记录失败: {e}", 'ERROR')
                messagebox.showerror("导出失败", f"导出历史记录失败:\n{e}")

    def clear_history(self):
        """清空所有历史记录"""
        if messagebox.askyesno("清空历史记录", "您确定要清空所有历史识别记录吗？此操作不可逆！"):
            if self.result_manager.clear_history(confirm=False):
                self.refresh_history()
                self.update_enhanced_stats()
                self.log_message("🧹 所有历史记录已成功清空。", 'SUCCESS')
            else:
                self.log_message("❌ 清空历史记录失败。", 'ERROR')

    def search_history_dialog(self):
        """打开搜索历史记录的对话框"""
        search_window = tk.Toplevel(self.root)
        search_window.title("搜索历史记录")
        search_window.geometry("450x200")
        search_window.transient(self.root)
        search_window.grab_set()

        search_frame = ttk.Frame(search_window, padding=design.get_spacing('4'))
        search_frame.pack(fill='both', expand=True)

        tk.Label(search_frame, text="搜索关键词:", bg=design.get_color('neutral', '50')).pack(anchor='w', pady=(0, design.get_spacing('1')))
        search_entry = ttk.Entry(search_frame, width=50)
        search_entry.pack(fill='x', pady=(0, design.get_spacing('2')))
        search_entry.focus_set()

        search_in_text_var = tk.BooleanVar(value=True)
        search_in_filename_var = tk.BooleanVar(value=True)

        ttk.Checkbutton(search_frame, text="在识别文本中搜索", variable=search_in_text_var).pack(anchor='w')
        ttk.Checkbutton(search_frame, text="在图片名称中搜索", variable=search_in_filename_var).pack(anchor='w')

        def perform_search():
            query = search_entry.get()
            if not query:
                return

            results = self.result_manager.search_results(
                query,
                search_in_text=search_in_text_var.get(),
                search_in_filename=search_in_filename_var.get()
            )
            
            # 清空当前历史树并显示搜索结果
            self.history_tree.delete(*self.history_tree.get_children())
            if not results:
                self.history_tree.insert('', 'end', values=("", "无搜索结果", "", "", "", "", "", ""))
            else:
                for i, entry in enumerate(results):
                    components = entry.get('cvocr_components', {})
                    used_components_str = "+".join([k.replace('_used', '') for k, v in components.items() if v]) if components else "Tesseract"
                    status = "成功" 
                    if 'error' in entry.get('results', {}):
                        status = "错误"
                    elif entry.get('total_blocks', 0) == 0 and entry.get('full_text', '') == '':
                        status = "无文本"
                    self.history_tree.insert('', 'end', values=(
                        datetime.fromisoformat(entry['timestamp']).strftime('%Y-%m-%d %H:%M:%S'),
                        entry['image_name'],
                        entry.get('total_blocks', 0),
                        entry.get('total_characters', 0),
                        f"{entry.get('avg_confidence', 0):.1f}%",
                        used_components_str,
                        status,
                        f"{entry.get('processing_time', 0):.2f}s"
                    ), iid=entry['id'])
            
            self.log_message(f"🔍 历史记录搜索完成，找到 {len(results)} 条匹配项。", 'INFO')
            messagebox.showinfo("搜索完成", f"找到 {len(results)} 条匹配项。")
            search_window.destroy()
            self.notebook.select(3) # 切换到历史记录标签页

        search_button = tk.Button(search_frame, text="搜索", command=perform_search)
        design.apply_button_style(search_button, 'primary')
        search_button.pack(pady=(design.get_spacing('2'), 0))
        search_entry.bind("<Return>", lambda event: perform_search())

    def on_history_double_click(self, event):
        """处理历史记录双击事件，重新加载并显示结果"""
        item_id = self.history_tree.focus()
        if not item_id:
            return

        result_id = self.history_tree.item(item_id, 'iid')
        entry = self.result_manager.get_result_by_id(result_id)

        if entry:
            self.log_message(f"🔄 正在从历史记录加载: {entry['image_name']}", 'INFO')
            self.current_image_path = entry['image_path']
            # Pass the entry's 'results' dict directly as if it came from recognition
            self._handle_recognition_result(entry['image_path'], entry['results'], "从历史记录加载")
            self.notebook.select(0) # 切换到图片预览

    def on_history_right_click(self, event):
        """处理历史记录右键点击事件，显示上下文菜单"""
        item_id = self.history_tree.identify_row(event.y)
        if not item_id:
            return

        self.history_tree.selection_set(item_id) # 选中右键点击的项
        result_id = self.history_tree.item(item_id, 'iid')
        entry = self.result_manager.get_result_by_id(result_id)

        if entry:
            menu = tk.Menu(self.root, tearoff=0)
            menu.add_command(label="🔄 加载此结果", command=lambda: self.on_history_double_click(None))
            menu.add_command(label="📁 在文件浏览器中打开图片", command=lambda: self.show_in_explorer_for_history(entry['image_path']))
            menu.add_command(label="📋 复制纯文本", command=lambda: self.copy_text_from_history(entry['full_text']))
            menu.add_command(label="📤 导出此结果 (JSON)", command=lambda: self.export_single_history_result(entry))
            menu.add_command(label="🗑️ 删除此历史记录", command=lambda: self.delete_history_item(result_id))
            
            menu.post(event.x_root, event.y_root)

    def show_in_explorer_for_history(self, image_path: str):
        """为历史记录中的图片在文件浏览器中打开"""
        self.current_image_path = image_path # 暂时设置当前图片路径
        self.show_in_explorer()
        
    def copy_text_from_history(self, text: str):
        """复制历史记录中的文本到剪贴板"""
        if text:
            try:
                self.root.clipboard_clear()
                self.root.clipboard_append(text)
                self.log_message("📋 历史记录文本已复制到剪贴板。", 'SUCCESS')
            except Exception as e:
                self.log_message(f"❌ 复制历史记录文本失败: {e}", 'ERROR')
                messagebox.showerror("复制失败", f"无法复制文本到剪贴板:\n{e}")
        else:
            messagebox.showwarning("无文本", "该历史记录没有文本内容。")

    def export_single_history_result(self, entry: Dict):
        """导出单个历史记录结果"""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON文件", "*.json"), ("文本文件", "*.txt"), ("所有文件", "*.*")],
            title=f"导出 '{entry['image_name']}' 的结果"
        )
        
        if file_path:
            try:
                extension = os.path.splitext(file_path)[1].lower()
                
                if extension == ".json":
                    with open(file_path, 'w', encoding='utf-8') as f:
                        json.dump(entry, f, ensure_ascii=False, indent=2)
                elif extension == ".txt":
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(entry.get('full_text', ''))
                else:
                    messagebox.showwarning("不支持的格式", "请选择JSON或TXT格式进行导出。")
                    self.log_message(f"❌ 导出历史结果失败：不支持的文件格式 {extension}。", 'ERROR')
                    return
                
                self.log_message(f"📤 历史结果已导出到: {file_path}", 'SUCCESS')
                messagebox.showinfo("导出成功", f"结果已成功导出到:\n{file_path}")
            except Exception as e:
                self.log_message(f"❌ 导出历史结果失败: {e}", 'ERROR')
                messagebox.showerror("导出失败", f"导出结果失败:\n{e}")

    def delete_history_item(self, result_id: str):
        """从历史记录中删除指定的项"""
        if messagebox.askyesno("删除历史记录", "您确定要删除此历史记录吗？此操作不可逆！"):
            # 在 result_manager 中删除
            for i, entry in enumerate(self.result_manager.history):
                if entry['id'] == result_id:
                    del self.result_manager.history[i]
                    self.result_manager._results_cache.pop(result_id, None)
                    break
            self.refresh_history()
            self.update_enhanced_stats()
            self.log_message(f"🗑️ 已删除历史记录项: {result_id}", 'INFO')

    def update_enhanced_stats(self):
        """更新统计信息标签页的显示内容"""
        stats = self.result_manager.get_stats()
        cvocr_perf = self.cvocr_manager.get_performance_stats() # Get performance stats from manager itself
        img_proc_perf = self.image_processor.get_processing_stats()

        stats_report = []
        stats_report.append("--- CVOCR 综合统计报告 ---\n")
        stats_report.append(f"报告生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        stats_report.append("-" * 40 + "\n")

        stats_report.append("=== 识别总览 ===\n")
        stats_report.append(f"总识别任务数: {cvocr_perf.get('total_recognitions', 0)}\n") # Use cvocr_perf for consistency
        stats_report.append(f"成功识别任务数: {cvocr_perf.get('successful_recognitions', 0)}\n")
        stats_report.append(f"失败识别任务数: {cvocr_perf.get('failed_recognitions', 0)}\n")
        stats_report.append(f"成功率: {stats.get('success_rate', 0):.2f}%\n") # success_rate is calculated by result_manager
        stats_report.append(f"总字符数: {stats.get('total_characters_recognized', 0)}\n")
        stats_report.append(f"总处理时间: {stats.get('total_processing_time', 0):.2f} 秒\n")
        stats_report.append(f"平均处理时间/任务: {stats.get('average_processing_time', 0):.2f} 秒\n")
        stats_report.append(f"平均置信度: {stats.get('average_confidence', 0):.2f}%\n")
        stats_report.append("-" * 40 + "\n")

        stats_report.append("=== 语言分布 ===\n")
        if stats.get('language_distribution'):
            for lang, count in stats['language_distribution'].items():
                stats_report.append(f"  {lang}: {count} 次\n")
            stats_report.append(f"最常用语言: {stats.get('most_used_language', 'N/A')}\n")
        else:
            stats_report.append("  无语言统计数据。\n")
        stats_report.append("-" * 40 + "\n")

        stats_report.append("=== 组件使用情况 ===\n")
        if cvocr_perf.get('component_usage'): # Use cvocr_perf for consistency
            for comp, count in cvocr_perf['component_usage'].items():
                stats_report.append(f"  {comp}: {count} 次\n")
        else:
            stats_report.append("  无组件使用统计数据。\n")
        stats_report.append("-" * 40 + "\n")

        stats_report.append("=== 图像预处理统计 ===\n")
        stats_report.append(f"总预处理图像数: {img_proc_perf.get('total_processed', 0)}\n")
        stats_report.append(f"缓存命中次数: {img_proc_perf.get('cache_hits', 0)}\n")
        stats_report.append(f"缓存未命中次数: {img_proc_perf.get('cache_misses', 0)}\n")
        stats_report.append(f"缓存命中率: {img_proc_perf.get('cache_hit_rate', 0):.2f}%\n")
        stats_report.append(f"平均预处理时间: {img_proc_perf.get('average_processing_time', 0):.2f} 秒\n")
        stats_report.append("-" * 40 + "\n")

        self.stats_text.config(state='normal')
        self.stats_text.delete(1.0, tk.END)
        self.stats_text.insert(tk.END, "".join(stats_report))
        self.stats_text.config(state='disabled')
        
        self.log_message(f"📈 统计信息已更新。", 'INFO')

    def export_stats(self):
        """导出统计信息到文件"""
        stats = self.result_manager.get_stats()
        processor_stats = self.image_processor.get_processing_stats()
        cvocr_manager_perf_stats = self.cvocr_manager.get_performance_stats() # Get performance stats from manager

        export_data = {
            "timestamp": datetime.now().isoformat(),
            "cvocr_version": CVOCRConstants.VERSION,
            "recognition_overall_stats_from_result_manager": stats, # Renamed for clarity
            "cvocr_manager_performance_stats": cvocr_manager_perf_stats, # Added
            "preprocessing_stats": processor_stats
        }

        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON文件", "*.json"), ("所有文件", "*.*")],
            title="导出统计信息"
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    json.dump(export_data, f, ensure_ascii=False, indent=2)
                self.log_message(f"📊 统计信息已导出到: {file_path}", 'SUCCESS')
                messagebox.showinfo("导出成功", f"统计信息已成功导出到:\n{file_path}")
            except Exception as e:
                self.log_message(f"❌ 导出统计信息失败: {e}", 'ERROR')
                messagebox.showerror("导出失败", f"导出统计信息失败:\n{e}")

    def reset_stats(self):
        """重置所有统计信息"""
        if messagebox.askyesno("重置统计信息", "您确定要重置所有统计数据吗？此操作不可逆！"):
            self.result_manager.clear_history(confirm=False) # 清空历史会重置其统计
            self.cvocr_manager.clear_performance_stats()
            self.image_processor.clear_cache()
            self.update_enhanced_stats()
            self.log_message("🔄 所有统计数据和缓存已重置。", 'SUCCESS')

    def compare_images(self):
        """比较两张图片的处理效果（待实现复杂UI）"""
        messagebox.showinfo("功能待实现", "图片比较功能正在开发中，敬请期待！")
        self.log_message("ℹ️ 图片比较功能正在开发中。", 'INFO')

    def compare_methods(self):
        """比较不同OCR方法或配置的识别效果（待实现复杂UI）"""
        messagebox.showinfo("功能待实现", "方法比较功能正在开发中，敬请期待！")
        self.log_message("ℹ️ 方法比较功能正在开发中。", 'INFO')

    def clear_log(self):
        """清空日志显示区"""
        self.log_text.config(state='normal')
        self.log_text.delete(1.0, tk.END)
        self.log_text.config(state='disabled')
        self.log_message("🧹 日志已清空。", 'INFO')

    def save_log(self):
        """保存日志到文件"""
        log_content = self.log_text.get(1.0, tk.END).strip()
        if not log_content:
            messagebox.showwarning("无日志", "没有可保存的日志内容。")
            return
        
        file_path = filedialog.asksaveasfilename(
            defaultextension=".log",
            filetypes=[("日志文件", "*.log"), ("文本文件", "*.txt"), ("所有文件", "*.*")],
            title="保存日志"
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(log_content)
                self.log_message(f"💾 日志已保存到: {file_path}", 'SUCCESS')
                messagebox.showinfo("保存成功", f"日志已成功保存到:\n{file_path}")
            except Exception as e:
                self.log_message(f"❌ 保存日志失败: {e}", 'ERROR')
                messagebox.showerror("保存失败", f"保存日志失败:\n{e}")

    def on_closing(self):
        """处理窗口关闭事件，确保只执行一次"""
        # 如果正在关闭或已经关闭，则直接返回
        if self._is_closing:
            return

        self._is_closing = True
        
        try:
            # 1. 保存设置
            self._save_settings()
            self.log_message("👋 CVOCR增强版正在退出...", 'INFO')
        
            # 2. 干净地关闭后台线程和循环
            # 关闭 AsyncOCRProcessor 的线程池
            if hasattr(self, 'async_ocr_processor'):
                self.async_ocr_processor.shutdown()

            # 停止 asyncio 事件循环
            if self.loop and self.loop.is_running():
                # 提交一个任务来停止循环
                self.loop.call_soon_threadsafe(self.loop.stop)
                # 等待事件循环线程结束，避免主进程提前退出
                if hasattr(self, 'async_loop_thread') and self.async_loop_thread.is_alive():
                    self.async_loop_thread.join(timeout=2) # 等待最多2秒
                    if self.async_loop_thread.is_alive():
                        logger.warning("Asyncio event loop thread did not terminate gracefully.")
                # 在主线程中关闭循环
                self.loop.close()
                logger.info("Asyncio event loop closed.")
        except Exception as e:
            logger.error(f"Error during shutdown cleanup: {e}", exc_info=True)
        finally:
            # 3. 最后销毁Tkinter窗口
            # 确保即使清理失败，窗口也能被销毁
            if self.root:
                self.root.destroy()

    def add_debug_monitoring(self):
        """添加调试监控，定期更新性能显示"""
        self.root.after(1000, self._update_performance_display) # 每秒更新一次

    def _update_performance_display(self):
        """更新性能指标显示"""
        cvocr_perf = self.cvocr_manager.get_performance_stats()
        img_proc_perf = self.image_processor.get_processing_stats()

        # CVOCR识别性能
        avg_rec_time = cvocr_perf.get('average_recognition_time', 0)
        total_recs = cvocr_perf.get('total_recognitions', 0)
        success_recs = cvocr_perf.get('successful_recognitions', 0)
        rec_rate = (success_recs / total_recs * 100) if total_recs > 0 else 0

        # 图像处理缓存性能
        cache_hit_rate = img_proc_perf.get('cache_hit_rate', 0)
        
        perf_text = (
            f"识别: {total_recs}次 | 成功: {success_recs} ({rec_rate:.1f}%) | "
            f"平均识别: {avg_rec_time:.2f}s | 缓存命中: {cache_hit_rate:.1f}%"
        )
        self.performance_label.config(text=perf_text)
        
        self.root.after(1000, self._update_performance_display) # 再次调度

    def on_text_result_double_click(self, event):
        """处理详细结果树的双击事件，在图片上高亮对应区域"""
        item_id = self.results_tree.focus()
        if not item_id or not self.current_image_path:
            return

        idx = int(item_id.split('_')[1]) # 从 item_id (e.g., "block_0") 获取索引
        current_results_data = self.result_manager.current_results
        if not current_results_data or idx >= len(current_results_data.get('text_blocks', [])):
            return

        selected_block = current_results_data['text_blocks'][idx]
        bbox = selected_block.get('bbox')
        
        # --- 核心修正开始 ---
        # 增加对 bbox 和关键实例变量的检查
        if not bbox or len(bbox) != 4:
             self.log_message(f"无法高亮：文本块 '{selected_block['text'][:20]}...' 缺少有效的边界框信息。", "WARNING")
             return
             
        if not hasattr(self, '_last_display_scale_ratio_x') or \
           not hasattr(self, '_last_display_x_offset'):
            self.log_message("无法高亮：缺少图像显示参数。请确保图片已正确显示。", "WARNING")
            return
        
        # 清除旧的高亮框
        self.image_canvas.delete("highlight_bbox")

        # 从实例变量获取显示参数
        scale_ratio_x = self._last_display_scale_ratio_x
        scale_ratio_y = self._last_display_scale_ratio_y
        x_offset = self._last_display_x_offset
        y_offset = self._last_display_y_offset

        # 转换原始坐标到画布坐标
        x1_orig, y1_orig, x2_orig, y2_orig = bbox
        x1_canvas = int(x1_orig * scale_ratio_x + x_offset)
        y1_canvas = int(y1_orig * scale_ratio_y + y_offset)
        x2_canvas = int(x2_orig * scale_ratio_x + x_offset)
        y2_canvas = int(y2_orig * scale_ratio_y + y_offset)
        
        # 绘制高亮矩形框
        self.image_canvas.create_rectangle(
            x1_canvas, y1_canvas, x2_canvas, y2_canvas, 
            outline='blue', width=3, tags="highlight_bbox"
        )
        
        # --- 滚动逻辑保持不变，但基于正确的坐标 ---
        canvas_width = self.image_canvas.winfo_width()
        canvas_height = self.image_canvas.winfo_height()
        
        if self._last_original_image_size:
            original_img_width, original_img_height = self._last_original_image_size
            display_width = int(original_img_width * scale_ratio_x)
            display_height = int(original_img_height * scale_ratio_y)
            
            # 确保 display_width 和 display_height 不为零
            if display_width > 0 and display_height > 0:
                scroll_x = (x1_canvas + (x2_canvas - x1_canvas) / 2 - canvas_width / 2) / display_width
                scroll_y = (y1_canvas + (y2_canvas - y1_canvas) / 2 - canvas_height / 2) / display_height
                
                scroll_x = max(0.0, min(1.0, scroll_x))
                scroll_y = max(0.0, min(1.0, scroll_y))

                self.image_canvas.xview_moveto(scroll_x)
                self.image_canvas.yview_moveto(scroll_y)
        # --- 核心修正结束 ---

        self.log_message(f"高亮显示文本块: {selected_block['text'][:20]}...", 'INFO')
        self.notebook.select(0) # 切换到图片预览

    def on_text_result_right_click(self, event):
        """处理详细结果树的右键点击事件"""
        item_id = self.results_tree.identify_row(event.y)
        if not item_id:
            return
        
        self.results_tree.selection_set(item_id)
        result_idx = int(self.results_tree.item(item_id, 'iid').split('_')[1])
        current_results_data = self.result_manager.current_results
        
        if current_results_data and result_idx < len(current_results_data.get('text_blocks', [])):
            selected_block = current_results_data['text_blocks'][result_idx]
            
            menu = tk.Menu(self.root, tearoff=0)
            menu.add_command(label="📋 复制文本", command=lambda: self.copy_text_from_history(selected_block['text']))
            menu.add_command(label="🔍 在图片上高亮显示", command=lambda: self.on_text_result_double_click(None))
            menu.add_command(label="🗑️ 从结果中删除 (待实现)", state='disabled') # 复杂功能，暂禁用
            menu.post(event.x_root, event.y_root)

    def filter_results_dialog(self):
        """打开过滤详细识别结果的对话框"""
        messagebox.showinfo("功能待实现", "过滤结果功能正在开发中，敬请期待！")
        self.log_message("ℹ️ 过滤结果功能正在开发中。", 'INFO')

    def sort_results_dialog(self):
        """打开排序详细识别结果的对话框"""
        messagebox.showinfo("功能待实现", "排序结果功能正在开发中，敬请期待！")
        self.log_message("ℹ️ 排序结果功能正在开发中。", 'INFO')
    
    def generate_test_images(self):
        """生成测试图片 (现在是异步协程)"""
        async def generate_worker_async():
            self.log_message("🎨 正在生成测试图片...", 'INFO')
            try:
                # 阻塞操作放入线程池
                success, message = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    TextTestImageGenerator.create_text_test_image,
                    "cvocr_test_2025.jpg",
                    True
                )
                self.root.after(0, self._handle_generate_test_image_result, success, message)
            except Exception as e:
                error_msg = f"生成测试图片失败: {e}\n{traceback.format_exc()}"
                self.root.after(0, self._handle_generate_test_image_result, False, error_msg)
            finally:
                self.root.after(0, self.set_processing, False)
        
        self.set_processing(True)
        self.loop.call_soon_threadsafe(self.loop.create_task, generate_worker_async())
    def _handle_generate_test_image_result(self, success: bool, message: str):
        """处理生成测试图片的结果"""
        if success:
            self.log_message(f"✅ {message}", 'SUCCESS')
            self.current_image_path = "cvocr_test_2025.jpg"
            self.display_image(self.current_image_path)
            messagebox.showinfo("生成成功", message)
        else:
            self.log_message(f"❌ {message}", 'ERROR')
            messagebox.showerror("生成失败", message)
    def preview_region_preprocessing(self):
        """启动一个异步任务，以预览单个文本区域的精细化预处理效果。"""
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行其他操作，请稍候。")
            return
        if not self.current_image_path:
            messagebox.showwarning("未选择图片", "请先选择一张图片。")
            return
        if not self.cvocr_manager.is_initialized or not self.cvocr_manager.text_detector:
            messagebox.showerror("引擎未就绪", "请先初始化CVOCR引擎。")
            return

        self.set_processing(True)
        self.log_message("🔬 正在生成区域预处理预览...", 'INFO')

        async def preview_worker_async():
            try:
                # 步骤1: 获取预处理后的整张图
                preprocess_options = {key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar))}
                
                task_preprocess = functools.partial(
                    self.image_processor.intelligent_preprocess_image,
                    self.current_image_path,
                    **preprocess_options
                )
                processed_image_np, _, _ = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    task_preprocess
                )

                if processed_image_np is None: 
                    raise Exception("图像预处理失败。")

                # 步骤2: 在预处理图上进行分割，找到区域
                enabled_algorithms = self._get_enabled_segmentation_algorithms()
                if not enabled_algorithms: 
                    raise Exception("请至少选择一种高级分割技术。")
                
                current_config = {key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar))}

                self.cvocr_manager.text_detector.config.update(current_config)
                
                task_detect = functools.partial(
                    self.cvocr_manager.text_detector.detect_text_regions_advanced,
                    processed_image_np, 
                    enabled_algorithms
                )
                regions, _ = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    task_detect
                )
                
                if not regions:
                    self.log_message("⚠️ 预览中止：使用当前分割技术未检测到任何文本区域。", "WARNING")
                    self.root.after(0, messagebox.showwarning, "预览中止", 
                                    "使用当前选择的高级分割技术未能在此图片上检测到任何文本区域。\n\n"
                                    "请尝试：\n"
                                    "1. 勾选不同的分割技术（如“改进MSER”）。\n"
                                    "2. 调整“高级设置”中的预处理选项。\n"
                                    "3. 点击“预览分割结果”查看整体分割效果。")
                    return

                # 步骤3: 选取第一个区域并进行精细化预处理
                region_box = regions[0]
                rect = cv2.minAreaRect(region_box)
                center, (width, height), angle = rect

                # --- 最终版智能旋转逻辑 ---
                # 步骤1: 确保 width >= height，标准化矩形描述
                if width < height:
                    width, height = height, width
                    swapped = True
                else:
                    swapped = False
                
                # 步骤2: 仅当矩形原本是瘦长的垂直形状时，才应用90度旋转校正
                aspect_ratio = width / height if height > 0 else 0
                if swapped and aspect_ratio > 1.5:
                    angle += 90
                # --- 逻辑结束 ---

                width, height = int(width), int(height)
                
                M = cv2.getRotationMatrix2D(center, angle, 1.0)
                warped_bgr = cv2.warpAffine(processed_image_np, M, (processed_image_np.shape[1], processed_image_np.shape[0]))
                cropped_bgr = cv2.getRectSubPix(warped_bgr, (width, height), center)

                if cropped_bgr is None or cropped_bgr.size == 0:
                    raise Exception("无法从图像中切割出有效的文本区域。")
                
                # 应用精细化预处理
                gray_cropped = cv2.cvtColor(cropped_bgr, cv2.COLOR_BGR2GRAY)
                h, w = gray_cropped.shape
                if h > 0 and (h < 24 or h > 64):
                    scale = 40.0 / h
                    gray_cropped = cv2.resize(gray_cropped, (0,0), fx=scale, fy=scale, interpolation=cv2.INTER_CUBIC)
                
                clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(4, 4))
                enhanced = clahe.apply(gray_cropped)
                _, binarized = cv2.threshold(enhanced, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
                bordered = cv2.copyMakeBorder(binarized, 8, 8, 8, 8, cv2.BORDER_CONSTANT, value=[255])
                
                original_region_pil = Image.fromarray(cv2.cvtColor(cropped_bgr, cv2.COLOR_BGR2RGB))
                processed_region_pil = Image.fromarray(bordered)

                self.root.after(0, self._show_region_preview_window, original_region_pil, processed_region_pil)

            except Exception as e:
                logger.error(f"生成区域预处理预览时发生异常: {e}", exc_info=True)
                self.root.after(0, messagebox.showerror, "预览失败", f"生成预览失败: {e}\n\n请检查日志获取详细信息。")
            finally:
                self.root.after(0, self.set_processing, False)

        self.loop.call_soon_threadsafe(self.loop.create_task, preview_worker_async())
    
    
    def _show_region_preview_window(self, original_region: Image.Image, processed_region: Image.Image):
        """创建一个新窗口来对比显示单个文本区域的预处理前后效果。"""
        preview_window = tk.Toplevel(self.root)
        preview_window.title("Tesseract精细化预处理效果预览")
        preview_window.geometry("800x400")
        preview_window.transient(self.root)
        preview_window.grab_set()

        main_frame = ttk.Frame(preview_window, padding=design.get_spacing('4'))
        main_frame.pack(fill='both', expand=True)

        image_frame = ttk.Frame(main_frame)
        image_frame.pack(fill='both', expand=True)

        original_frame = ttk.LabelFrame(image_frame, text="处理前", padding=design.get_spacing('2'))
        original_frame.pack(side='left', fill='both', expand=True, padx=(0, design.get_spacing('2')))
        original_label = tk.Label(original_frame, bg=design.get_color('neutral', '100'))
        original_label.pack(fill='both', expand=True)

        processed_frame = ttk.LabelFrame(image_frame, text="处理后 (送入Tesseract)", padding=design.get_spacing('2'))
        processed_frame.pack(side='right', fill='both', expand=True, padx=(design.get_spacing('2'), 0))
        processed_label = tk.Label(processed_frame, bg=design.get_color('neutral', '100'))
        processed_label.pack(fill='both', expand=True)

        def resize_and_display(label: tk.Label, img: Image.Image):
            max_size = 300
            img.thumbnail((max_size, max_size), Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(img)
            label.config(image=photo)
            label.image = photo

        resize_and_display(original_label, original_region)
        resize_and_display(processed_label, processed_region)
        
        info_label = tk.Label(main_frame, text="这是对一个样本区域应用精细化预处理（缩放、增强、二值化、加边框）后的效果。\n您可以在主界面取消勾选“启用精细化预处理”来跳过此步骤。",
                              wraplength=750, justify='center', bg=design.get_color('neutral', '50'))
        info_label.pack(pady=(design.get_spacing('2'), 0))
    def preview_merge_effect(self):
        """启动一个异步任务，以预览智能行合并的效果。"""
        if self.processing:
            messagebox.showwarning("处理中", "当前正在进行其他操作，请稍候。")
            return
        if not self.current_image_path:
            messagebox.showwarning("未选择图片", "请先选择一张图片。")
            return
        if not self.cvocr_manager.is_initialized or not self.cvocr_manager.text_detector:
            messagebox.showerror("引擎未就绪", "请先初始化CVOCR引擎。")
            return

        self.set_processing(True)
        self.log_message("🔬 正在生成智能行合并效果预览...", 'INFO')

        async def preview_worker_async():
            try:
                # 步骤1: 预处理图像
                self.log_message("  -> [合并预览] 步骤1: 开始预处理图像...", "DEBUG")
                preprocess_options = {key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar))}
                
                # 使用 functools.partial 将函数和其参数打包成一个无参数的可调用对象
                task_preprocess = functools.partial(
                    self.image_processor.intelligent_preprocess_image,
                    self.current_image_path,
                    **preprocess_options
                )
                
                processed_image_np, _, _ = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    task_preprocess
                )

                if processed_image_np is None: 
                    raise Exception("图像预处理失败。")
                self.log_message("  -> [合并预览] 步骤1: 预处理图像完成。", "DEBUG")

                enabled_algorithms = self._get_enabled_segmentation_algorithms()
                if not enabled_algorithms: 
                    raise Exception("请至少选择一种高级分割技术。")

                # 步骤2a: 执行分割，但不进行合并
                self.log_message("  -> [合并预览] 步骤2a: 执行分割 (不合并)...", "DEBUG")
                unmerged_config = {key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar))}
                unmerged_config['enable_smart_line_merge'] = False
                self.cvocr_manager.text_detector.config.update(unmerged_config)
                
                task_unmerged_detect = functools.partial(
                    self.cvocr_manager.text_detector.detect_text_regions_advanced,
                    processed_image_np,
                    enabled_algorithms
                )
                unmerged_regions, _ = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    task_unmerged_detect
                )
                self.log_message(f"  -> [合并预览] 步骤2a: 分割完成，找到 {len(unmerged_regions)} 个区域。", "DEBUG")

                # 步骤2b: 执行分割，并进行合并
                self.log_message("  -> [合并预览] 步骤2b: 执行分割 (合并)...", "DEBUG")
                merged_config = {key: var.get() for key, var in self.settings.items() if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar))}
                merged_config['enable_smart_line_merge'] = True
                self.cvocr_manager.text_detector.config.update(merged_config)
                
                task_merged_detect = functools.partial(
                    self.cvocr_manager.text_detector.detect_text_regions_advanced,
                    processed_image_np,
                    enabled_algorithms
                )
                merged_regions, _ = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    task_merged_detect
                )
                self.log_message(f"  -> [合并预览] 步骤2b: 合并完成，得到 {len(merged_regions)} 个区域。", "DEBUG")
                
                self.log_message(f"  -> 分割结果: {len(unmerged_regions)} (合并前) -> {len(merged_regions)} (合并后)", "INFO")

                # 步骤3: 绘制对比图像
                self.log_message("  -> [合并预览] 步骤3: 正在绘制预览图像...", "DEBUG")
                img_unmerged = processed_image_np.copy()
                img_merged = processed_image_np.copy()
                
                if len(img_unmerged.shape) == 2: img_unmerged = cv2.cvtColor(img_unmerged, cv2.COLOR_GRAY2BGR)
                if len(img_merged.shape) == 2: img_merged = cv2.cvtColor(img_merged, cv2.COLOR_GRAY2BGR)
                
                if unmerged_regions:
                    cv2.polylines(img_unmerged, [np.array(r, np.int32) for r in unmerged_regions], True, (255, 0, 0), 2) # 红色：未合并
                if merged_regions:
                    cv2.polylines(img_merged, [np.array(r, np.int32) for r in merged_regions], True, (0, 255, 0), 2) # 绿色：已合并

                img_unmerged_pil = Image.fromarray(cv2.cvtColor(img_unmerged, cv2.COLOR_BGR2RGB))
                img_merged_pil = Image.fromarray(cv2.cvtColor(img_merged, cv2.COLOR_BGR2RGB))
                
                metadata = {
                    'unmerged_count': len(unmerged_regions),
                    'merged_count': len(merged_regions)
                }
                
                # 步骤4: 在主线程显示预览窗口
                self.log_message("  -> [合并预览] 步骤4: 即将显示预览窗口...", "DEBUG")
                self.root.after(0, self._show_merge_preview_window, img_unmerged_pil, img_merged_pil, metadata)

            except Exception as e:
                logger.error(f"生成合并预览时发生异常: {e}", exc_info=True)
                self.root.after(0, messagebox.showerror, "预览失败", f"生成预览失败: {e}\n\n请检查日志获取详细信息。")
            finally:
                self.root.after(0, self.set_processing, False)

        self.loop.call_soon_threadsafe(self.loop.create_task, preview_worker_async())
    
    
    
    def _show_merge_preview_window(self, img_unmerged: Image.Image, img_merged: Image.Image, metadata: Dict):
        """创建新窗口对比显示行合并前后的效果。"""
        preview_window = tk.Toplevel(self.root)
        preview_window.title("智能行合并效果预览")
        preview_window.geometry("1600x800")
        preview_window.transient(self.root)
        preview_window.grab_set()

        main_frame = ttk.Frame(preview_window, padding=design.get_spacing('4'))
        main_frame.pack(fill='both', expand=True)

        image_frame = ttk.Frame(main_frame)
        image_frame.pack(fill='both', expand=True)

        unmerged_frame = ttk.LabelFrame(image_frame, text=f"合并前 (红色框) - {metadata['unmerged_count']} 个区域", padding=design.get_spacing('2'))
        unmerged_frame.pack(side='left', fill='both', expand=True, padx=(0, design.get_spacing('2')))
        unmerged_canvas = tk.Canvas(unmerged_frame, bg='black')
        unmerged_canvas.pack(fill='both', expand=True)

        merged_frame = ttk.LabelFrame(image_frame, text=f"合并后 (绿色框) - {metadata['merged_count']} 个区域", padding=design.get_spacing('2'))
        merged_frame.pack(side='right', fill='both', expand=True, padx=(design.get_spacing('2'), 0))
        merged_canvas = tk.Canvas(merged_frame, bg='black')
        merged_canvas.pack(fill='both', expand=True)

        def resize_and_display(canvas: tk.Canvas, img: Image.Image):
            canvas.update_idletasks()
            canvas_w, canvas_h = canvas.winfo_width(), canvas.winfo_height()
            if canvas_w <= 1 or canvas_h <= 1: return
            
            img_w, img_h = img.size
            scale = min(canvas_w / img_w, canvas_h / img_h)
            new_w, new_h = int(img_w * scale), int(img_h * scale)
            
            resized = img.resize((new_w, new_h), Image.Resampling.LANCZOS)
            photo = ImageTk.PhotoImage(resized)
            canvas.image = photo 
            x_offset = (canvas_w - new_w) // 2
            y_offset = (canvas_h - new_h) // 2
            canvas.create_image(x_offset, y_offset, image=photo, anchor='nw')

        preview_window.after(100, lambda: [
            resize_and_display(unmerged_canvas, img_unmerged),
            resize_and_display(merged_canvas, img_merged),
            unmerged_canvas.bind('<Configure>', lambda e: resize_and_display(unmerged_canvas, img_unmerged)),
            merged_canvas.bind('<Configure>', lambda e: resize_and_display(merged_canvas, img_merged))
        ])
if __name__ == "__main__":
    app_instance = None
    try:
        # 创建Tkinter根窗口
        root = tk.Tk()
        # 实例化主GUI应用类
        app_instance = EnhancedCVOCRGUI(root)
        
        # 启动Tkinter的主事件循环。
        # 此循环会一直运行，直到窗口被关闭。
        # 窗口关闭事件由 EnhancedCVOCRGUI 内部的 protocol("WM_DELETE_WINDOW", ...) 捕获，
        # 并调用 on_closing 方法来执行所有清理工作。
        root.mainloop()
        
    except Exception as e:
        # 捕获应用启动或运行期间发生的任何未处理的致命错误
        logger.critical(f"应用启动或运行时发生致命错误: {e}\n{traceback.format_exc()}", exc_info=True)
        
        # 尝试弹出一个简单的错误窗口，以便用户了解情况
        try:
            # --- 额外优化：确保在创建 messagebox 之前有 root 窗口 ---
            # 如果 root 创建失败，之前的 messagebox 会报错
            # 这里我们创建一个临时的 root 来显示错误信息
            root_exists = 'root' in locals() and isinstance(root, tk.Tk) and root.winfo_exists()
            
            if not root_exists:
                error_root = tk.Tk()
                error_root.withdraw() # 隐藏主窗口
                messagebox.showerror("CVOCR应用错误", f"应用发生致命错误: {e}\n请检查日志文件 'cvocr_gui.log' 获取更多详情。", parent=error_root)
                error_root.destroy()
            else:
                 messagebox.showerror("CVOCR应用错误", f"应用发生致命错误: {e}\n请检查日志文件 'cvocr_gui.log' 获取更多详情。")
        except Exception as tk_e:
            # 如果连messagebox都无法弹出（例如在无头环境中），就在控制台打印最终错误
            print(f"CRITICAL ERROR (cannot show messagebox, check log file): {e}\nTraceback: {traceback.format_exc()}")
            logger.critical(f"无法显示Tkinter错误对话框: {tk_e}", exc_info=True)
    
    # --- 修正: 移除了整个 finally 块 ---
    # 关闭逻辑已完全由 on_closing 方法通过窗口协议触发，这里不再需要。
    # 这可以防止在应用已销毁后再次调用 on_closing 导致的 TclError。
    logger.info("Application mainloop has finished. Process is exiting.")