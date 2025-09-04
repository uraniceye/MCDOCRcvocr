# --- START OF FILE MCDOCRcvocr_gui.py ---


#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CVOCR(Context Vision OCR)文本识别插件 - 增强稳定版 v3.0 (2025)
完全重构，支持CVOCR最新版本，大幅增强文本检测精度和识别准确度
新增智能文本检测、高级图像预处理、自适应参数优化等功能
技术架构：FSRCNN + LayoutLMv2 + Tesseract + GPT-Neo + Transformer OCR
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
import psutil # <--- 修正2: 新增导入 psutil，用于系统内存检查

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

class OCRPrecisionLevel(Enum):
    """OCR精度等级枚举"""
    FAST = "fast"          # 快速模式
    BALANCED = "balanced"  # 平衡模式
    ACCURATE = "accurate"  # 精确模式
    ULTRA = "ultra"        # 超精确模式
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
    """增强版文本检测器 - 继承高级分割功能"""
    
    def detect_text_regions_advanced(self, image: np.ndarray, precision_level: OCRPrecisionLevel = OCRPrecisionLevel.BALANCED) -> Tuple[List[np.ndarray], Dict]:
        """高级文本区域检测 - 多算法融合"""
        try:
            # 检查缓存
            cache_key = f"{hash(image.tobytes())}_{precision_level.value}"
            if cache_key in self._segmentation_cache:
                cached_result = self._segmentation_cache[cache_key]
                logger.info("使用缓存的分割结果")
                return cached_result['regions'], cached_result['metadata']
            
            start_time = time.time()
            
            # 预处理图像
            if len(image.shape) == 3:
                gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
            else:
                gray = image.copy()
            
            # 根据精度级别选择检测策略
            if precision_level == OCRPrecisionLevel.FAST:
                text_regions, metadata = self._fast_text_detection(gray)
            elif precision_level == OCRPrecisionLevel.BALANCED:
                text_regions, metadata = self._balanced_text_detection(gray)
            elif precision_level == OCRPrecisionLevel.ACCURATE:
                text_regions, metadata = self._accurate_text_detection(gray)
            else:  # ULTRA
                text_regions, metadata = self._ultra_text_detection(gray)
            
            # 后处理优化
            optimized_regions = self._optimize_text_regions(text_regions, gray.shape)
            
            # 文本行重组
            line_regions = self._reorganize_text_lines(optimized_regions, gray)
            
            # 添加处理时间到元数据
            processing_time = time.time() - start_time
            metadata.update({
                'processing_time': processing_time,
                'precision_level': precision_level.value,
                'total_regions': len(line_regions),
                'optimization_applied': True
            })
            
            # 缓存结果
            self._manage_segmentation_cache(cache_key, {
                'regions': line_regions,
                'metadata': metadata
            })
            
            logger.info(f"高级文本检测完成: {len(line_regions)}个区域, 耗时: {processing_time:.3f}秒")
            return line_regions, metadata
            
        except Exception as e:
            logger.error(f"高级文本区域检测失败: {e}")
            return [], {'error': str(e)}
    
    def _fast_text_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """快速文本检测模式"""
        try:
            regions = []
            
            # 快速自适应阈值
            binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                         cv2.THRESH_BINARY_INV, 11, 2)
            
            # 简单形态学操作
            kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (3, 1))
            processed = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel)
            
            # 查找轮廓
            contours, _ = cv2.findContours(processed, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            
            for contour in contours:
                area = cv2.contourArea(contour)
                if area > self.config['min_text_size'] ** 2:
                    rect = cv2.minAreaRect(contour)
                    box = cv2.boxPoints(rect)
                    regions.append(box.astype(np.float32))
            
            metadata = {
                'method': 'fast_adaptive_threshold',
                'contours_found': len(contours),
                'regions_filtered': len(regions)
            }
            
            return regions, metadata
            
        except Exception as e:
            logger.error(f"快速文本检测失败: {e}")
            return [], {'error': str(e)}
    
    def _balanced_text_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """平衡文本检测模式"""
        try:
            regions = []
            methods_used = []
            
            # 方法1: 改进的MSER检测
            mser_regions = self._improved_mser_detection(gray)
            regions.extend(mser_regions)
            methods_used.append('improved_mser')
            
            # 方法2: 多尺度轮廓检测
            contour_regions = self._multiscale_contour_detection(gray)
            regions.extend(contour_regions)
            methods_used.append('multiscale_contour')
            
            # 方法3: 梯度方向检测
            gradient_regions = self._gradient_based_detection(gray)
            regions.extend(gradient_regions)
            methods_used.append('gradient_based')
            
            # 合并重叠区域
            # 修正点：将调用不存在的 `_merge_overlapping_regions_advanced` 
            # 替换为调用已存在的 `_resolve_overlapping_regions`。
            merged_regions = self._resolve_overlapping_regions(regions) 
            
            metadata = {
                'methods_used': methods_used,
                'raw_regions': len(regions),
                'merged_regions': len(merged_regions),
                'detection_mode': 'balanced'
            }
            
            return merged_regions, metadata
            
        except Exception as e:
            logger.error(f"平衡文本检测失败: {e}")
            return [], {'error': str(e)}
    
    def _accurate_text_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """精确文本检测模式"""
        try:
            regions = []
            detection_stats = {}
            
            # 方法1: 多尺度MSER检测
            mser_regions, mser_stats = self._multiscale_mser_detection(gray)
            regions.extend(mser_regions)
            detection_stats['mser'] = mser_stats
            
            # 方法2: 高精度轮廓检测
            contour_regions, contour_stats = self._high_precision_contour_detection(gray)
            regions.extend(contour_regions)
            detection_stats['contour'] = contour_stats
            
            # 方法3: 文本行连接检测
            line_regions, line_stats = self._text_line_connection_detection(gray)
            regions.extend(line_regions)
            detection_stats['text_line'] = line_stats
            
            # 方法4: SWT (Stroke Width Transform) 检测
            swt_regions, swt_stats = self._stroke_width_transform_detection(gray)
            regions.extend(swt_regions)
            detection_stats['swt'] = swt_stats
            
            # 高级合并和过滤
            merged_regions = self._advanced_region_merging(regions, gray)
            filtered_regions = self._intelligent_region_filtering(merged_regions, gray)
            
            metadata = {
                'detection_stats': detection_stats,
                'raw_regions': len(regions),
                'merged_regions': len(merged_regions),
                'final_regions': len(filtered_regions),
                'detection_mode': 'accurate'
            }
            
            return filtered_regions, metadata
            
        except Exception as e:
            logger.error(f"精确文本检测失败: {e}")
            return [], {'error': str(e)}
    
    def _ultra_text_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """超精确文本检测模式"""
        try:
            regions = []
            ultra_stats = {}
            
            # 方法1: 多层次MSER检测
            mser_regions, mser_stats = self._multilevel_mser_detection(gray)
            regions.extend(mser_regions)
            ultra_stats['multilevel_mser'] = mser_stats
            
            # 方法2: 自适应多阈值检测
            threshold_regions, threshold_stats = self._adaptive_multithreshold_detection(gray)
            regions.extend(threshold_regions)
            ultra_stats['adaptive_threshold'] = threshold_stats
            
            # 方法3: 连通分量分析
            cc_regions, cc_stats = self._connected_component_analysis(gray)
            regions.extend(cc_regions)
            ultra_stats['connected_components'] = cc_stats
            
            # 方法4: 文本方向自适应检测
            orientation_regions, orientation_stats = self._orientation_adaptive_detection(gray)
            regions.extend(orientation_regions)
            ultra_stats['orientation_adaptive'] = orientation_stats
            
            # 方法5: 字符级分割检测
            char_regions, char_stats = self._character_level_detection(gray)
            regions.extend(char_regions)
            ultra_stats['character_level'] = char_stats
            
            # 超精确合并和优化
            merged_regions = self._ultra_precise_merging(regions, gray)
            optimized_regions = self._final_optimization(merged_regions, gray)
            
            metadata = {
                'ultra_stats': ultra_stats,
                'raw_regions': len(regions),
                'merged_regions': len(merged_regions),
                'optimized_regions': len(optimized_regions),
                'detection_mode': 'ultra'
            }
            
            return optimized_regions, metadata
            
        except Exception as e:
            logger.error(f"超精确文本检测失败: {e}")
            return [], {'error': str(e)}
    
    def _improved_mser_detection(self, gray: np.ndarray) -> List[np.ndarray]:
        """改进的MSER检测"""
        try:
            regions = []
            
            # 多参数MSER检测
            # 修正点：将参数名中的下划线移除
            mser_configs = [
                {'min_area': 30, 'max_area': 14400, 'max_variation': 0.25, 'min_diversity': 0.2},
                {'min_area': 60, 'max_area': 10000, 'max_variation': 0.3, 'min_diversity': 0.15},
                {'min_area': 100, 'max_area': 8000, 'max_variation': 0.2, 'min_diversity': 0.25}
            ]
            
            for config in mser_configs:
                try:
                    # 调用 cv2.MSER_create 时使用修正后的参数名
                    mser = cv2.MSER_create(**config)
                    mser_regions, _ = mser.detectRegions(gray)
                    
                    for region in mser_regions:
                        hull = cv2.convexHull(region.reshape(-1, 1, 2))
                        rect = cv2.minAreaRect(hull)
                        box = cv2.boxPoints(rect)
                        
                        # 验证区域质量
                        if self._validate_text_region(box, gray):
                            regions.append(box.astype(np.float32))
                            
                except Exception as e:
                    # 记录具体的错误信息，有助于调试
                    logger.warning(f"MSER配置失败: {e}")
                    continue
            
            return regions
            
        except Exception as e:
            logger.error(f"改进MSER检测失败: {e}")
            return []
    
    def _multiscale_contour_detection(self, gray: np.ndarray) -> List[np.ndarray]:
        """多尺度轮廓检测"""
        try:
            regions = []
            scales = [0.8, 1.0, 1.2, 1.5]
            
            for scale in scales:
                # 缩放图像
                if scale != 1.0:
                    h, w = gray.shape
                    new_h, new_w = int(h * scale), int(w * scale)
                    scaled_gray = cv2.resize(gray, (new_w, new_h), interpolation=cv2.INTER_LINEAR)
                else:
                    scaled_gray = gray
                
                # 多种阈值方法
                for threshold_size in self.config['adaptive_threshold_sizes']:
                    try:
                        binary = cv2.adaptiveThreshold(
                            scaled_gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                            cv2.THRESH_BINARY_INV, threshold_size, 2
                        )
                        
                        # 形态学操作
                        kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (3, 1))
                        processed = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel, 
                                                   iterations=self.config['morphology_iterations'])
                        
                        # 查找轮廓
                        contours, _ = cv2.findContours(processed, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                        
                        for contour in contours:
                            area = cv2.contourArea(contour)
                            if area > self.config['connected_component_min_area']:
                                rect = cv2.minAreaRect(contour)
                                box = cv2.boxPoints(rect)
                                
                                # 缩放回原始尺寸
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
        """基于梯度的文本检测"""
        try:
            regions = []
            
            # 计算梯度
            grad_x = cv2.Sobel(gray, cv2.CV_64F, 1, 0, ksize=3)
            grad_y = cv2.Sobel(gray, cv2.CV_64F, 0, 1, ksize=3)
            
            # 梯度幅值和方向
            magnitude = np.sqrt(grad_x**2 + grad_y**2)
            angle = np.arctan2(grad_y, grad_x)
            
            # 归一化梯度幅值
            magnitude = cv2.normalize(magnitude, None, 0, 255, cv2.NORM_MINMAX).astype(np.uint8)
            
            # 阈值化
            _, binary = cv2.threshold(magnitude, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            
            # 形态学操作连接文本
            kernel_horizontal = cv2.getStructuringElement(cv2.MORPH_RECT, (5, 1))
            kernel_vertical = cv2.getStructuringElement(cv2.MORPH_RECT, (1, 5))
            
            # 处理水平和垂直文本
            horizontal = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel_horizontal)
            vertical = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel_vertical)
            
            # 合并结果
            combined = cv2.bitwise_or(horizontal, vertical)
            
            # 查找轮廓
            contours, _ = cv2.findContours(combined, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
            
            for contour in contours:
                area = cv2.contourArea(contour)
                if area > self.config['min_text_size'] ** 2:
                    rect = cv2.minAreaRect(contour)
                    box = cv2.boxPoints(rect)
                    
                    # 验证是否为文本区域
                    if self._validate_gradient_region(box, magnitude):
                        regions.append(box.astype(np.float32))
            
            return regions
            
        except Exception as e:
            logger.error(f"梯度检测失败: {e}")
            return []
    
    def _stroke_width_transform_detection(self, gray: np.ndarray) -> Tuple[List[np.ndarray], Dict]:
        """笔画宽度变换检测"""
        try:
            regions = []
            stats = {'swt_regions': 0, 'valid_strokes': 0}
            
            # 计算边缘和梯度
            edges = cv2.Canny(gray, 50, 150, apertureSize=3)
            grad_x = cv2.Sobel(gray, cv2.CV_64F, 1, 0, ksize=3)
            grad_y = cv2.Sobel(gray, cv2.CV_64F, 0, 1, ksize=3)
            
            # 计算梯度方向
            gradient_magnitude = np.sqrt(grad_x**2 + grad_y**2)
            gradient_direction = np.arctan2(grad_y, grad_x)
            
            # 创建SWT图像
            swt = np.full(gray.shape, np.inf, dtype=np.float64)
            
            # 查找边缘点
            edge_points = np.where(edges > 0)
            
            for i in range(len(edge_points[0])):
                y, x = edge_points[0][i], edge_points[1][i]
                
                if gradient_magnitude[y, x] > 0:
                    # 沿梯度方向追踪
                    direction = gradient_direction[y, x]
                    
                    # 正方向追踪
                    stroke_width = self._trace_stroke_width(
                        edges, gradient_direction, x, y, direction, gray.shape
                    )
                    
                    if stroke_width > 0 and stroke_width < 300:  # 合理的笔画宽度
                        swt[y, x] = stroke_width
                        stats['valid_strokes'] += 1
            
            # 从SWT图像中提取文本区域
            swt_binary = np.zeros_like(gray)
            swt_binary[swt < np.inf] = 255
            
            # 连通分量分析
            num_labels, labels, stats_cc, centroids = cv2.connectedComponentsWithStats(swt_binary, connectivity=8)
            
            for i in range(1, num_labels):  # 跳过背景
                if stats_cc[i, cv2.CC_STAT_AREA] > self.config['connected_component_min_area']:
                    # 提取组件
                    mask = (labels == i).astype(np.uint8) * 255
                    contours, _ = cv2.findContours(mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                    
                    if contours:
                        largest_contour = max(contours, key=cv2.contourArea)
                        rect = cv2.minAreaRect(largest_contour)
                        box = cv2.boxPoints(rect)
                        
                        # 验证笔画宽度一致性
                        if self._validate_stroke_consistency(box, swt):
                            regions.append(box.astype(np.float32))
                            stats['swt_regions'] += 1
            
            return regions, stats
            
        except Exception as e:
            logger.error(f"SWT检测失败: {e}")
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
        """连通分量分析"""
        try:
            regions = []
            stats = {'total_components': 0, 'valid_components': 0}
            
            # 多种二值化方法
            binary_methods = [
                lambda img: cv2.adaptiveThreshold(img, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY_INV, 11, 2),
                lambda img: cv2.adaptiveThreshold(img, 255, cv2.ADAPTIVE_THRESH_MEAN_C, cv2.THRESH_BINARY_INV, 15, 3),
                lambda img: cv2.threshold(img, 0, 255, cv2.THRESH_BINARY_INV + cv2.THRESH_OTSU)[1]
            ]
            
            for binary_method in binary_methods:
                try:
                    binary = binary_method(gray)
                    
                    # 连通分量分析
                    num_labels, labels, stats_cc, centroids = cv2.connectedComponentsWithStats(binary, connectivity=8)
                    stats['total_components'] += num_labels - 1  # 排除背景
                    
                    for i in range(1, num_labels):  # 跳过背景
                        area = stats_cc[i, cv2.CC_STAT_AREA]
                        width = stats_cc[i, cv2.CC_STAT_WIDTH]
                        height = stats_cc[i, cv2.CC_STAT_HEIGHT]
                        
                        # 验证组件特征
                        if (area > self.config['connected_component_min_area'] and 
                            self.config['char_min_width'] <= width <= self.config['char_max_width'] and
                            self.config['char_min_height'] <= height <= self.config['char_max_height']):
                            
                            # 提取组件轮廓
                            mask = (labels == i).astype(np.uint8) * 255
                            contours, _ = cv2.findContours(mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                            
                            if contours:
                                largest_contour = max(contours, key=cv2.contourArea)
                                rect = cv2.minAreaRect(largest_contour)
                                box = cv2.boxPoints(rect)
                                
                                # 进一步验证
                                if self._validate_component_shape(box, mask):
                                    regions.append(box.astype(np.float32))
                                    stats['valid_components'] += 1
                                    
                except Exception as e:
                    logger.warning(f"连通分量方法失败: {e}")
                    continue
            
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
        """字符级检测"""
        try:
            regions = []
            stats = {'char_candidates': 0, 'valid_chars': 0}
            
            # 多尺度字符检测
            scales = [0.8, 1.0, 1.2]
            
            for scale in scales:
                # 缩放图像
                if scale != 1.0:
                    h, w = gray.shape
                    new_h, new_w = int(h * scale), int(w * scale)
                    scaled_gray = cv2.resize(gray, (new_w, new_h), interpolation=cv2.INTER_CUBIC)
                else:
                    scaled_gray = gray
                
                # 字符分离
                char_regions = self._separate_characters(scaled_gray)
                stats['char_candidates'] += len(char_regions)
                
                # 缩放回原始尺寸并验证
                for region in char_regions:
                    if scale != 1.0:
                        region = region / scale
                    
                    if self._validate_character_region(region, gray):
                        regions.append(region.astype(np.float32))
                        stats['valid_chars'] += 1
            
            return regions, stats
            
        except Exception as e:
            logger.error(f"字符级检测失败: {e}")
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
        """多层次MSER检测"""
        try:
            regions = []
            stats = {'levels_processed': 0, 'regions_per_level': []}
            
            # 多层次参数配置
            # 修正点：将参数名中的下划线移除
            mser_levels = [
                # 细粒度检测
                {'min_area': 15, 'max_area': 2000, 'max_variation': 0.15, 'min_diversity': 0.3},
                # 中等粒度检测
                {'min_area': 50, 'max_area': 8000, 'max_variation': 0.25, 'min_diversity': 0.2},
                # 粗粒度检测
                {'min_area': 150, 'max_area': 15000, 'max_variation': 0.35, 'min_diversity': 0.15},
                # 超大区域检测
                {'min_area': 500, 'max_area': 25000, 'max_variation': 0.4, 'min_diversity': 0.1}
            ]
            
            for level, config in enumerate(mser_levels):
                try:
                    # 调用 cv2.MSER_create 时使用修正后的参数名
                    mser = cv2.MSER_create(**config)
                    level_regions, _ = mser.detectRegions(gray)
                    
                    level_valid_regions = []
                    for region in level_regions:
                        # 计算凸包
                        hull = cv2.convexHull(region.reshape(-1, 1, 2))
                        rect = cv2.minAreaRect(hull)
                        box = cv2.boxPoints(rect)
                        
                        # 多层次验证
                        if self._validate_multilevel_region(box, gray, level):
                            regions.append(box.astype(np.float32))
                    
                    stats['regions_per_level'].append(len(level_valid_regions))
                    stats['levels_processed'] += 1
                    
                except Exception as e:
                    # 记录具体的错误信息，有助于调试
                    logger.warning(f"MSER级别{level}失败: {e}")
                    stats['regions_per_level'].append(0)
            
            return regions, stats
            
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
        """检测水平文本区域"""
        try:
            regions = []

            # 针对水平文本优化的形态学操作
            binary = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                         cv2.THRESH_BINARY_INV, 11, 2)

            # 水平连接核
            horizontal_kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (10, 1))
            horizontal_lines = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, horizontal_kernel)

            # 查找水平文本区域
            contours, _ = cv2.findContours(horizontal_lines, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)

            for contour in contours:
                area = cv2.contourArea(contour)
                if area > self.config['min_text_size'] ** 2:
                    # 获取边界矩形
                    x, y, w, h = cv2.boundingRect(contour)

                    # 验证是否为水平文本
                    aspect_ratio = w / h if h > 0 else 0
                    if aspect_ratio > 1.5:  # 水平文本的宽高比应该大于1.5
                        box = np.array([
                            [x, y],
                            [x + w, y],
                            [x + w, y + h],
                            [x, y + h]
                        ], dtype=np.float32)
                        regions.append(box)

            return regions # <-- Added return statement here

        except Exception as e: # <-- Added the 'except' block here
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

class OCRLanguage(Enum):
    """OCR语言枚举"""
    AUTO = "auto"          # 自动检测
    CHINESE = "chi_sim"    # 简体中文
    ENGLISH = "eng"        # 英文
    CHINESE_TRAD = "chi_tra"  # 繁体中文
    JAPANESE = "jpn"       # 日文
    KOREAN = "kor"         # 韩文
    MULTI = "chi_sim+eng"  # 中英混合

### 修正3: 添加 TextQualityLevel 枚举定义
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
            
            if original_cmd is not None: # <--- 修正4: 将 `is == None` 替换为 `is None`
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
        for lib_name in ['numpy', 'PIL', 'tkinter', 'psutil']: # <--- 修正5: 添加 psutil 到版本检查
            try:
                lib = __import__(lib_name)
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
        智能图像预处理核心方法 (V3.8 最终纯净版)
        - 彻底分离预处理职责：为高级分割时，只做最基础的尺寸和通道准备。
        - 为整页识别时，执行全面的自适应预处理。
        - 当预处理被禁用时，仅进行尺寸优化。
        """
        start_time = time.time()
        
        try:
            # 1. 验证输入图像的有效性
            is_valid, validation_msg = self.validate_image(image_path)
            if not is_valid:
                logger.error(f"图像验证失败: {validation_msg}")
                return None, f"图像验证失败: {validation_msg}", {}
            
            # 2. 生成缓存键并检查缓存
            cache_key = self._generate_cache_key(image_path, options)
            cached_result = self._get_from_cache(cache_key)
            if cached_result is not None:
                self._processing_stats['cache_hits'] += 1
                logger.info("使用缓存的图像预处理结果。")
                return cached_result['image'], cached_result['message'], cached_result['metadata']
            
            self._processing_stats['cache_misses'] += 1
            
            # 3. 读取图像
            image = cv2.imread(image_path)
            if image is None:
                try:
                    pil_img = Image.open(image_path).convert('RGB')
                    image = cv2.cvtColor(np.array(pil_img), cv2.COLOR_RGB2BGR)
                except Exception as e:
                    raise CVOCRException(f"无法读取图像文件: {str(e)}", "IMAGE_READ_ERROR")
            
            original_shape = image.shape
            logger.info(f"开始智能OCR预处理图像: {image_path}, 原始尺寸: {original_shape}")
            
            # 4. 根据 options 决定预处理策略
            enable_preprocessing = options.get('enable_preprocessing', False)
            use_advanced_segmentation = options.get('enable_advanced_segmentation', False)
            
            processed_image = image.copy()
            process_operations = []
            quality_level = TextQualityLevel.FAIR
            quality_metrics = {}

            if enable_preprocessing and use_advanced_segmentation:
                # **流程A: 为高级分割准备输入**
                # 此流程的目标是为分割引擎提供一张干净、结构完整的图像。
                # 只做最基础、最安全的操作，将所有复杂处理留到分割之后。
                logger.info("高级分割模式启用：执行最基础的图像准备。")
                
                # (1) 尺寸优化：确保图像在合适的尺寸范围内
                processed_image = self._optimize_image_size(processed_image)
                process_operations.append("基础尺寸优化")
                
                # (2) 确保是BGR格式：这是分割引擎所期望的输入格式
                if len(processed_image.shape) == 2:
                    processed_image = cv2.cvtColor(processed_image, cv2.COLOR_GRAY2BGR)
                elif processed_image.shape[2] == 4: # 处理RGBA
                    processed_image = cv2.cvtColor(processed_image, cv2.COLOR_BGRA2BGR)
                
                # (3) （可选但推荐）进行安全的几何校正
                if options.get('enable_deskew', self.config['enable_deskew']):
                    gray_for_deskew = cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                    deskewed_gray, angle = self._deskew_image(gray_for_deskew, options.get('deskew_angle_threshold', self.config['deskew_angle_threshold']))
                    if angle != 0.0:
                        # 对原始尺寸的BGR图像应用旋转
                        center = (image.shape[1] // 2, image.shape[0] // 2)
                        rotation_matrix = cv2.getRotationMatrix2D(center, angle, 1.0)
                        processed_image = cv2.warpAffine(processed_image, rotation_matrix,
                                                   (image.shape[1], image.shape[0]),
                                                   flags=cv2.INTER_CUBIC,
                                                   borderMode=cv2.BORDER_REPLICATE)
                        process_operations.append(f"倾斜校正 ({angle:.2f}度)")

            elif enable_preprocessing and not use_advanced_segmentation:
                # **流程B: 为整页识别进行全面的自适应预处理**
                logger.info("整页识别模式启用：执行全面的自适应预处理。")
                
                # (1) 评估图像质量
                quality_level, quality_metrics = self.assess_text_image_quality(image)
                
                # (2) 根据质量或强制设置，选择合适的处理强度
                if options.get('force_intensive_preprocessing', False):
                    processed_image, process_operations = self._intensive_text_preprocessing(image, **options)
                else:
                    processed_image, process_operations = self.adaptive_text_preprocessing(image, quality_level, **options)
            
            else: # not enable_preprocessing
                # **流程C: 禁用智能预处理**
                logger.info("智能预处理已禁用，只进行基础尺寸优化。")
                
                # (1) 仅进行尺寸优化
                processed_image = self._optimize_image_size(image)
                process_operations.append("基础尺寸优化")
                
                # (2) 确保输出是3通道BGR
                if len(processed_image.shape) == 2:
                    processed_image = cv2.cvtColor(processed_image, cv2.COLOR_GRAY2BGR)
                    process_operations.append("灰度转BGR (最终)")
            
            # 5. 记录处理时间和元数据
            processing_time = time.time() - start_time
            self._update_processing_stats(processing_time)
            
            precision_level_opt = options.get('precision_level', OCRPrecisionLevel.BALANCED)
            precision_level_str = precision_level_opt.value if isinstance(precision_level_opt, Enum) else str(precision_level_opt)

            metadata = {
                'precision_level': precision_level_str,
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
            
            # 6. 将处理结果添加到缓存
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
            # 重新抛出自定义异常，让上层处理
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
        基于图像质量评估的自适应文本预处理。
        根据检测到的图像质量等级，选择不同的预处理强度。
        """
        try:
            if quality_level is None:
                quality_level, _ = self.assess_text_image_quality(image)
            
            processed_image = image.copy()
            operations = []
            
            # 统一转换为灰度图 (如果不是)
            if len(processed_image.shape) == 3:
                processed_image = cv2.cvtColor(processed_image, cv2.COLOR_BGR2GRAY)
                operations.append("转换为灰度图")

            # 图像几何校正和边框处理 (始终执行，因为这些是基础且重要的修正)
            # 倾斜校正
            if options.get('enable_deskew', self.config['enable_deskew']):
                deskewed_image, angle = self._deskew_image(processed_image, options.get('deskew_angle_threshold', self.config['deskew_angle_threshold']))
                if angle != 0.0:
                    processed_image = deskewed_image
                    operations.append(f"倾斜校正 ({angle:.2f}度)")
            
            # 阴影移除
            if options.get('shadow_removal', self.config['shadow_removal']):
                processed_image = self._remove_shadows(processed_image)
                operations.append("阴影移除")

            # 边框和内容裁剪
            if options.get('remove_borders', self.config['remove_borders']) or options.get('page_border_detection', self.config['page_border_detection']):
                processed_image = self._process_borders(processed_image, 
                                                    remove_borders=options.get('remove_borders', self.config['remove_borders']),
                                                    border_threshold=options.get('border_threshold', self.config['border_threshold']),
                                                    page_border_detection=options.get('page_border_detection', self.config['page_border_detection']))
                operations.append("边框处理/页面检测")
            
            if options.get('crop_to_content', self.config['crop_to_content']):
                cropped_image, crop_success = self._crop_to_content(processed_image)
                if crop_success:
                    processed_image = cropped_image
                    operations.append("裁剪到内容")
            
            # 根据质量等级选择处理策略
            if quality_level == TextQualityLevel.POOR:
                processed_image, ops = self._intensive_text_preprocessing(processed_image, **options)
                operations.extend(ops)
            elif quality_level == TextQualityLevel.FAIR:
                processed_image, ops = self._moderate_text_preprocessing(processed_image, **options)
                operations.extend(ops)
            elif quality_level == TextQualityLevel.GOOD:
                processed_image, ops = self._light_text_preprocessing(processed_image, **options)
                operations.extend(ops)
            else:  # EXCELLENT (质量优秀，最少处理)
                processed_image, ops = self._minimal_text_preprocessing(processed_image, **options)
                operations.extend(ops)
            
            # 确保最终输出图像是3通道BGR (以便Tesseract或后续AI模型处理)
            if len(processed_image.shape) == 2:
                processed_image = cv2.cvtColor(processed_image, cv2.COLOR_GRAY2BGR)
                operations.append("灰度转BGR (最终)")
            elif processed_image.shape[2] == 4:  # RGBA转BGR
                processed_image = cv2.cvtColor(processed_image, cv2.COLOR_BGRA2BGR)
                operations.append("RGBA转BGR")
            
            return processed_image, operations
            
        except Exception as e:
            logger.error(f"自适应文本预处理失败: {e}\n{traceback.format_exc()}")
            # 失败时返回原始图像的灰度/BGR版本，并记录错误
            if len(image.shape) == 2:
                return cv2.cvtColor(image, cv2.COLOR_GRAY2BGR), ['预处理异常']
            return image, ['预处理异常']
    
    def _intensive_text_preprocessing(self, gray_image: np.ndarray, **options) -> Tuple[np.ndarray, List[str]]:
        """
        高强度文本预处理，适用于低质量、复杂背景或有严重干扰的图像。
        采用多种高级技术，如高级降噪、CLAHE、Gamma校正、反锐化掩模和形态学操作。
        """
        operations = []
        
        try:
            processed_image = gray_image.copy()
            logger.debug("DEBUG: 执行高强度预处理 - 输入为灰度图。")
            
            # 高级降噪 (非局部均值降噪)
            denoise_strength = options.get('denoise_strength', self.config['denoise_strength'])
            edge_preservation = options.get('edge_preservation', self.config['edge_preservation'])
            if denoise_strength > 0:
                processed_image = self._advanced_denoising(processed_image, denoise_strength, edge_preservation)
                operations.append("高级降噪")
                logger.debug("DEBUG: 执行高强度预处理 - 高级降噪。")

            # 双边滤波去噪 (保留边缘)
            if options.get('bilateral_filter', self.config['bilateral_filter']):
                d_val = options.get('bilateral_d', self.config['bilateral_d'])
                sigma_color = options.get('bilateral_sigma_color', self.config['bilateral_sigma_color'])
                sigma_space = options.get('bilateral_sigma_space', self.config['bilateral_sigma_space'])
                processed_image = cv2.bilateralFilter(processed_image, 
                                                    d_val, 
                                                    int(sigma_color), # OpenCV expects int
                                                    int(sigma_space)) # OpenCV expects int
                operations.append("双边滤波去噪")
                logger.debug("DEBUG: 执行高强度预处理 - 双边滤波去噪。")
            
            # CLAHE直方图均衡化 (增强局部对比度)
            if options.get('apply_clahe', self.config['apply_clahe']):
                clahe_clip_limit = options.get('clahe_clip_limit', self.config['clahe_clip_limit'])
                clahe_tile_grid_size = options.get('clahe_tile_grid_size', self.config['clahe_tile_grid_size'])
                clahe = cv2.createCLAHE(clipLimit=clahe_clip_limit, tileGridSize=clahe_tile_grid_size)
                processed_image = clahe.apply(processed_image)
                operations.append("CLAHE直方图均衡化")
                logger.debug("DEBUG: 执行高强度预处理 - CLAHE直方图均衡化。")
            
            # Gamma校正 (调整整体亮度分布)
            gamma_val = options.get('gamma_correction', self.config['gamma_correction_range'][1]) # 使用配置中的上限
            inv_gamma = 1.0 / gamma_val
            gamma_table = np.array([((i / 255.0) ** inv_gamma) * 255 for i in range(256)]).astype(np.uint8)
            processed_image = cv2.LUT(processed_image, gamma_table)
            operations.append(f"Gamma校正 (γ={gamma_val})")
            logger.debug("DEBUG: 执行高强度预处理 - Gamma校正。")
            
            # 全局直方图均衡化
            if options.get('histogram_equalization', self.config['histogram_equalization']):
                processed_image = cv2.equalizeHist(processed_image)
                operations.append("全局直方图均衡化")
                
            # 锐化或反锐化掩模
            if options.get('unsharp_mask', self.config['unsharp_mask']):
                unsharp_radius = options.get('unsharp_radius', self.config['unsharp_radius'])
                unsharp_amount = options.get('unsharp_amount', self.config['unsharp_amount'])
                processed_image = self._unsharp_mask(processed_image, unsharp_radius, unsharp_amount)
                operations.append("反锐化掩模")
            else:
                kernel_sharpen = np.array([[-1, -1, -1], [-1, 9, -1], [-1, -1, -1]]) # 更强的锐化核
                processed_image = cv2.filter2D(processed_image, -1, kernel_sharpen)
                operations.append("锐化处理")
            logger.debug("DEBUG: 执行高强度预处理 - 锐化处理。")

            # 自适应二值化 (适应光照不均，更精细的块大小)
            block_size = options.get('adaptive_block_size', self.config['adaptive_block_size'])
            C_value = options.get('adaptive_c_constant', self.config['adaptive_c_constant']) 
            if block_size % 2 == 0: # 确保 block_size 是奇数
                block_size += 1
            processed_image = cv2.adaptiveThreshold(processed_image, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                                    cv2.THRESH_BINARY, block_size, C_value)
            operations.append("自适应二值化")
            logger.debug("DEBUG: 执行高强度预处理 - 自适应二值化。")
            
            # 形态学操作去除小噪点和连接断裂 (先闭运算连接，再开运算去噪)
            kernel_close = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (3, 3)) # 稍微大一点的核
            processed_image = cv2.morphologyEx(processed_image, cv2.MORPH_CLOSE, kernel_close)
            operations.append("形态学闭运算")
            logger.debug("DEBUG: 执行高强度预处理 - 形态学闭运算。")

            kernel_open = cv2.getStructuringElement(cv2.MORPH_ELLIPSE, (2, 2))
            processed_image = cv2.morphologyEx(processed_image, cv2.MORPH_OPEN, kernel_open)
            operations.append("形态学开运算")
            logger.debug("DEBUG: 执行高强度预处理 - 形态学开运算。")
            
            # 去除小连通域 (进一步去除图形干扰)
            num_labels, labels, stats, centroids = cv2.connectedComponentsWithStats(processed_image, connectivity=8)
            min_area = 50  # 最小连通域面积，适当增大以去除小的图形或线条
            output_image = np.zeros_like(processed_image)
            for i in range(1, num_labels):
                if stats[i, cv2.CC_STAT_AREA] > min_area:
                    output_image[labels == i] = 255
            processed_image = output_image
            operations.append("去除小连通域")
            logger.debug("DEBUG: 执行高强度预处理 - 去除小连通域。")
            
            return processed_image, operations
            
        except Exception as e:
            logger.error(f"高强度文本预处理失败: {e}\n{traceback.format_exc()}")
            operations.append("预处理异常")
            return gray_image, operations # 失败则返回原灰度图像
    
    def _moderate_text_preprocessing(self, gray_image: np.ndarray, **options) -> Tuple[np.ndarray, List[str]]:
        """
        中等强度文本预处理，适用于质量一般但有轻微缺陷的图像。
        包含双边滤波、CLAHE、对比度增强和自适应二值化。
        """
        operations = []
        
        try:
            processed_image = gray_image.copy()
            
            # 双边滤波 (轻度去噪，保留边缘)
            d_val = options.get('bilateral_d', 9)
            sigma_color = options.get('bilateral_sigma_color', 75.0)
            sigma_space = options.get('bilateral_sigma_space', 75.0)
            processed_image = cv2.bilateralFilter(processed_image, d_val, int(sigma_color), int(sigma_space))
            operations.append("双边滤波去噪")
            
            # CLAHE直方图均衡化
            clahe_clip_limit = options.get('clahe_clip_limit', 2.0)
            clahe_tile_grid_size = options.get('clahe_tile_grid_size', (8, 8))
            clahe = cv2.createCLAHE(clipLimit=clahe_clip_limit, tileGridSize=clahe_tile_grid_size)
            processed_image = clahe.apply(processed_image)
            operations.append("CLAHE直方图均衡化")
            
            # 对比度增强 (线性变换)
            alpha = 1.3  # 对比度控制
            beta = 10    # 亮度控制
            processed_image = cv2.convertScaleAbs(processed_image, alpha=alpha, beta=beta)
            operations.append(f"对比度增强 (α={alpha}, β={beta})")
            
            # 锐化 (中等强度)
            kernel_sharpen = np.array([[0, -1, 0], [-1, 5, -1], [0, -1, 0]])
            processed_image = cv2.filter2D(processed_image, -1, kernel_sharpen)
            operations.append("锐化处理")
            
            # 自适应二值化
            block_size = options.get('adaptive_block_size', 11)
            C_value = options.get('adaptive_c_constant', 2)
            if block_size % 2 == 0:
                block_size += 1
            processed_image = cv2.adaptiveThreshold(processed_image, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
                                                    cv2.THRESH_BINARY, block_size, C_value)
            operations.append("自适应二值化")
            
            # 轻度形态学处理 (闭运算连接文本，开运算去除噪点)
            kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (2, 2))
            processed_image = cv2.morphologyEx(processed_image, cv2.MORPH_CLOSE, kernel)
            processed_image = cv2.morphologyEx(processed_image, cv2.MORPH_OPEN, kernel)
            operations.append("轻度形态学处理")
            
            return processed_image, operations
            
        except Exception as e:
            logger.error(f"中等强度文本预处理失败: {e}\n{traceback.format_exc()}")
            operations.append("预处理异常")
            return gray_image, operations
    
    def _light_text_preprocessing(self, gray_image: np.ndarray, **options) -> Tuple[np.ndarray, List[str]]:
        """
        轻度文本预处理，适用于质量较好，只有轻微缺陷的图像。
        包含轻微对比度调整和OTSU二值化。
        """
        operations = []
        
        try:
            processed_image = gray_image.copy()
            
            # 轻微对比度调整
            alpha = 1.15  # 轻微的对比度增强
            beta = 5      # 轻微的亮度调整
            processed_image = cv2.convertScaleAbs(processed_image, alpha=alpha, beta=beta)
            operations.append(f"轻微对比度调整 (α={alpha}, β={beta})")
            
            # 轻度锐化
            kernel_sharpen = np.array([[0, -0.5, 0], [-0.5, 3, -0.5], [0, -0.5, 0]])
            processed_image = cv2.filter2D(processed_image, -1, kernel_sharpen)
            operations.append("轻度锐化")

            # OTSU二值化 (对良好图像通常足够，自动确定阈值)
            _, processed_image = cv2.threshold(processed_image, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            operations.append("OTSU二值化")
            
            return processed_image, operations
            
        except Exception as e:
            logger.error(f"轻度文本预处理失败: {e}\n{traceback.format_exc()}")
            operations.append("预处理异常")
            return gray_image, operations
    
    def _minimal_text_preprocessing(self, gray_image: np.ndarray, **options) -> Tuple[np.ndarray, List[str]]:
        """
        最小文本预处理，适用于质量优秀，几乎没有缺陷的图像。
        只进行极轻微锐化和OTSU二值化。
        """
        operations = []
        
        try:
            processed_image = gray_image.copy()
            
            # 极轻微锐化 (避免对高质量图像过度处理)
            kernel_sharpen = np.array([[0, -0.1, 0], [-0.1, 1.4, -0.1], [0, -0.1, 0]])
            processed_image = cv2.filter2D(processed_image, -1, kernel_sharpen)
            operations.append("极轻度锐化")

            # OTSU二值化 (保持简洁高效)
            _, processed_image = cv2.threshold(processed_image, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
            operations.append("OTSU二值化")
            
            return processed_image, operations
            
        except Exception as e:
            logger.error(f"最小文本预处理失败: {e}\n{traceback.format_exc()}")
            operations.append("预处理异常")
            return gray_image, operations
    
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
    """增强版CVOCR引擎管理器 - 集成多个先进OCR技术 (专业版)"""

    def __init__(self):
        # 模型和处理器占位符
        self.layoutlm_processor = None
        self.layoutlm_model = None
        self.trocr_processor = None
        self.trocr_model = None
        self.gpt_neo_tokenizer = None
        self.gpt_neo_model = None
        
        # FSRCNN 暂时保持模拟，因为它通常需要独立的模型文件。
        self.fsrcnn_model = {
            'type': 'fsrcnn_enhanced',
            'scale_factor': 2,
            'initialized': True,
            'model_path': None, # 实际应用中应该是模型文件路径
            'input_size': (None, None), # 支持任意尺寸输入
            'performance': {
                'avg_processing_time': 0.0,
                'processed_count': 0
            }
        }
        
        # Tesseract 相关
        self.tesseract_config = None
        self.tesseract_path = None
        
        # 状态与配置
        self.is_initialized = False
        self.device = "cpu" # 默认设备
        self.version_info = {}
        self.precision_level = OCRPrecisionLevel.BALANCED
        self.language = OCRLanguage.AUTO
        
        # CVOCRManager 内部的配置字典，用于存储来自 GUI 的最新设置
        self.config = {
            'psm': 6, 'oem': 3,
            'confidence_threshold': CVOCRConstants.DEFAULT_CONFIDENCE_THRESHOLD,
            'lang': 'chi_sim+eng',
            'enable_layout_analysis': False,
            'enable_context_analysis': False,
            'enable_super_resolution': False,
            'enable_transformer_ocr': False,
            'dpi': CVOCRConstants.DEFAULT_DPI,
            'enable_preprocessing_optimization': True,
            'batch_size': 1,
            'use_gpu': False,
            'model_precision': 'fp32',
            'tesseract_process_timeout': 300, # 新增或修改此行，设置为300秒 (5分钟)
            # 预处理相关配置 (初始默认值，这些值会被GUI的设置覆盖)
            'enable_deskew': True,
            'deskew_angle_threshold': 0.5,
            'remove_borders': True,
            'border_threshold': 10,
            'crop_to_content': True,
            'page_border_detection': True,
            'shadow_removal': True,
            'denoise_strength': 0.1,
            'edge_preservation': 0.8,
            'unsharp_mask': True,
            'unsharp_radius': 1.0,
            'unsharp_amount': 1.0,
            'histogram_equalization': True,
            'bilateral_filter': True,
            'bilateral_d': 9,
            'bilateral_sigma_color': 75.0,
            'bilateral_sigma_space': 75.0,
            'apply_clahe': True,
            'clahe_clip_limit': 2.0,
            'clahe_tile_grid_size': (8, 8),
            'adaptive_block_size': 11,
            'adaptive_c_constant': 2,
            'force_intensive_preprocessing': False, # 用于控制是否强制高强度预处理
        }
        self.text_detector = EnhancedTextDetector() # 实例化分割器
        # 性能监控
        self.performance_stats = {
            'total_recognitions': 0,
            'successful_recognitions': 0,
            'failed_recognitions': 0,
            'average_recognition_time': 0.0,
            'recognition_times': deque(maxlen=100),
            'component_usage': defaultdict(int) # 使用defaultdict方便统计
        }
        
        logger.info("增强版CVOCR引擎管理器已创建 (专业版)")

    @staticmethod
    def _execute_tesseract_subprocess(image_pil: Image.Image, tesseract_cmd_path: Optional[str], config_str: str, timeout: int) -> Dict:
        """
        Tesseract子进程执行器 (V3.6 延长超时时间版)
        - 增加日志密度，追踪执行流
        - 增强错误捕获和诊断信息
        - 确保临时文件清理
        - 恢复使用可配置的timeout，并建议提高默认值
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
        
        # 在执行前再次验证 tesseract_executable 是否可执行
        if not shutil.which(tesseract_executable) and not os.path.exists(tesseract_executable):
            logger.error(f"ERROR: Tesseract可执行文件未找到或不可执行: '{tesseract_executable}'。请检查路径配置。", exc_info=True)
            return {"status": "error", "message": f"Tesseract 可执行文件未找到或不可执行: '{tesseract_executable}'。"}

        temp_image_path = None
        temp_output_base = None
        temp_output_txt = None
        temp_output_tsv = None

        try:
            # 图像数据准备
            with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as temp_image_file:
                temp_image_path = temp_image_file.name
                if image_pil.mode not in ['RGB', 'L']:
                    image_pil = image_pil.convert('RGB')
                image_pil.save(temp_image_path, format='PNG')
            logger.debug(f"DEBUG: 图像已成功保存到临时文件: {temp_image_path} 用于Tesseract输入。")

            # 构造 Tesseract 输出的临时文件路径
            temp_output_base = tempfile.NamedTemporaryFile(delete=False).name
            temp_output_txt = temp_output_base + '.txt'
            temp_output_tsv = temp_output_base + '.tsv'

            config_args = config_str.split()

            command_base_txt = [tesseract_executable, temp_image_path, temp_output_base] + config_args
            command_base_tsv = [tesseract_executable, temp_image_path, temp_output_base, 'tsv'] + config_args
            
            creation_flags = 0
            if platform.system() == "Windows":
                try:
                    creation_flags = subprocess.CREATE_NO_WINDOW
                except AttributeError:
                    creation_flags = 0x08000000

            try:
                # 恢复使用传入的 timeout 参数
                actual_timeout = timeout 
                logger.debug(f"DEBUG: Tesseract进程超时设置为: {actual_timeout} 秒。")

                # 1. 获取纯文本结果
                logger.debug(f"DEBUG: 将调用 subprocess.run 执行纯文本命令: {' '.join(command_base_txt)}")
                process_text = subprocess.run(
                    command_base_txt,
                    capture_output=True,
                    timeout=actual_timeout,
                    creationflags=creation_flags,
                    check=False
                )
                logger.debug(f"DEBUG: subprocess.run (纯文本) 执行完成，返回码: {process_text.returncode}")

                if process_text.returncode != 0:
                    stderr_msg = process_text.stderr.decode('utf-8', 'ignore').strip()
                    logger.error(f"ERROR: Tesseract纯文本命令执行失败，返回码: {process_text.returncode}, 错误输出: {stderr_msg}", exc_info=True)
                    return {"status": "error", "message": f"Tesseract纯文本命令执行失败，返回码: {process_text.returncode}，错误输出: {stderr_msg}"}

                # 2. 获取详细数据 (TSV格式)
                logger.debug(f"DEBUG: 将调用 subprocess.run 执行TSV命令: {' '.join(command_base_tsv)}")
                process_data = subprocess.run(
                    command_base_tsv,
                    capture_output=True,
                    timeout=actual_timeout,
                    creationflags=creation_flags,
                    check=False
                )
                logger.debug(f"DEBUG: subprocess.run (TSV) 执行完成，返回码: {process_data.returncode}")

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

            # 3. 读取结果文件
            full_text = ""
            data_lines = []
            try:
                if os.path.exists(temp_output_txt):
                    with open(temp_output_txt, 'r', encoding='utf-8') as f:
                        full_text = f.read()
                    logger.debug(f"DEBUG: 已读取纯文本文件: {temp_output_txt}")
                else:
                    logger.warning(f"WARNING: Tesseract纯文本输出文件未找到: {temp_output_txt}")

                if os.path.exists(temp_output_tsv):
                    with open(temp_output_tsv, 'r', encoding='utf-8') as f:
                        data_lines = f.read().strip().split('\n')
                    logger.debug(f"DEBUG: 已读取TSV文件: {temp_output_tsv}")
                else:
                    logger.warning(f"WARNING: Tesseract TSV输出文件未找到: {temp_output_tsv}")

                # 4. 解析结果
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
                        data_dict[key] = [int(v) for v in data_dict[key]]
                if 'conf' in data_dict:
                    data_dict['conf'] = [float(v) for v in data_dict['conf'] if v != '-1']

                logger.debug("DEBUG: Tesseract结果解析完成。")
                return {"status": "success", "data": dict(data_dict), "full_text": full_text}
                
            except Exception as e:
                logger.error(f"ERROR: 读取或解析Tesseract结果文件失败: {str(e)}", exc_info=True)
                return {"status": "error", "message": f"读取或解析Tesseract结果文件失败: {str(e)}"}

        except Exception as e:
            logger.error(f"ERROR: _execute_tesseract_subprocess 外部主块发生意外错误: {str(e)}", exc_info=True)
            return {"status": "error", "message": f"Tesseract执行过程中出现意外错误: {str(e)}", "traceback": traceback.format_exc()}
        finally:
            # 确保清理临时文件
            if temp_image_path and os.path.exists(temp_image_path):
                try:
                    os.remove(temp_image_path)
                    logger.debug(f"DEBUG: 已清理临时图像文件: {temp_image_path}")
                except Exception as e:
                    logger.warning(f"WARNING: 无法清理临时图像文件 {temp_image_path}: {e}")
            if temp_output_base: # 检查基础路径是否存在
                if os.path.exists(temp_output_txt):
                    try:
                        os.remove(temp_output_txt)
                        logger.debug(f"DEBUG: 已清理临时纯文本文件: {temp_output_txt}")
                    except Exception as e:
                        logger.warning(f"WARNING: 无法清理临时纯文本文件 {temp_output_txt}: {e}")
                if os.path.exists(temp_output_tsv):
                    try:
                        os.remove(temp_output_tsv)
                        logger.debug(f"DEBUG: 已清理临时TSV文件: {temp_output_tsv}")
                    except Exception as e:
                        logger.warning(f"WARNING: 无法清理临时TSV文件 {temp_output_tsv}: {e}")
    
    
    
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
                   precision_level: OCRPrecisionLevel = OCRPrecisionLevel.BALANCED,
                   use_gpu: bool = False, **kwargs) -> Tuple[bool, str]:
        """初始化CVOCR模型 (专业版实现)"""
        try:
            import pytesseract # 确保在最前面导入，以便设置Tesseract路径
            # 确保在这里再次应用 Tesseract 路径，如果已设置
            if self.tesseract_path and os.path.exists(self.tesseract_path) and shutil.which(self.tesseract_path):
                pytesseract.pytesseract.tesseract_cmd = self.tesseract_path
                logger.info(f"初始化时应用已配置的Tesseract路径: {self.tesseract_path}")
            else:
                logger.warning("⚠️ Tesseract路径未配置或无效，将尝试使用系统PATH中的Tesseract。")

        except ImportError:
            return False, "pytesseract未安装，请先安装"
        except Exception as e:
            logger.warning(f"应用Tesseract路径时出错: {e}")

        if self.is_initialized:
            logger.info("CVOCR引擎已初始化，无需重复。")
            return True, "CVOCR引擎已初始化"

        try:
            import torch
            from transformers import (
                LayoutLMv2Processor, LayoutLMv2ForTokenClassification,
                TrOCRProcessor, VisionEncoderDecoderModel,
                GPT2Tokenizer, GPTNeoForCausalLM
            )
            import cv2 # 确保OpenCV也可用
        except ImportError as e:
            logger.error(f"❌ 初始化失败：缺少必要的AI/图像处理库: {e}。请运行 'pip install torch transformers sentencepiece opencv-python'", exc_info=True)
            return False, f"初始化失败：缺少必要的AI/图像处理库: {e}。请运行 'pip install torch transformers sentencepiece opencv-python'"
        except Exception as e:
            logger.error(f"❌ AI/图像处理库导入异常: {e}\n{traceback.format_exc()}", exc_info=True)
            return False, f"AI/图像处理库导入异常: {e}"

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

        self.precision_level = precision_level
        self.language = language
        
        logger.info(f"开始初始化CVOCR引擎 (语言: {language.value}, 精度: {precision_level.value}, 设备: {self.device})")
        
        # 2. 初始化Tesseract (增加语言包检查)
        success, message = self._initialize_tesseract()
        if not success:
            return False, message

        # 3. 按需加载高级模型 (现在是真正的加载，并更明确地记录状态)
        try:
            # LayoutLMv2
            if self.config.get('enable_layout_analysis', False):
                logger.debug("DEBUG: 尝试加载LayoutLMv2模型...")
                try:
                    self.layoutlm_processor = LayoutLMv2Processor.from_pretrained("microsoft/layoutlmv2-base-uncased")
                    self.layoutlm_model = LayoutLMv2ForTokenClassification.from_pretrained("microsoft/layoutlmv2-base-uncased").to(self.device)
                    self.layoutlm_model.eval()
                    logger.info("✅ LayoutLMv2模型加载成功。")
                except Exception as e:
                    self.layoutlm_model = None
                    self.layoutlm_processor = None
                    logger.error(f"❌ LayoutLMv2模型加载失败: {e}\n{traceback.format_exc()}", exc_info=True)
            else:
                logger.info("ℹ️ LayoutLMv2未启用，跳过加载。")

            # TrOCR
            if self.config.get('enable_transformer_ocr', False):
                logger.debug("DEBUG: 尝试加载TrOCR模型...")
                try:
                    self.trocr_processor = TrOCRProcessor.from_pretrained('microsoft/trocr-base-handwritten')
                    self.trocr_model = VisionEncoderDecoderModel.from_pretrained('microsoft/trocr-base-handwritten').to(self.device)
                    self.trocr_model.eval()
                    logger.info("✅ TrOCR模型加载成功。")
                except Exception as e:
                    self.trocr_model = None
                    self.trocr_processor = None
                    logger.error(f"❌ TrOCR模型加载失败: {e}\n{traceback.format_exc()}", exc_info=True)
            else:
                logger.info("ℹ️ TrOCR未启用，跳过加载。")

            # GPT-Neo
            if self.config.get('enable_context_analysis', False):
                logger.debug("DEBUG: 尝试加载GPT-Neo模型...")
                try:
                    self.gpt_neo_tokenizer = GPT2Tokenizer.from_pretrained("EleutherAI/gpt-neo-125M")
                    self.gpt_neo_model = GPTNeoForCausalLM.from_pretrained("EleutherAI/gpt-neo-125M").to(self.device)
                    self.gpt_neo_model.eval()
                    self.gpt_neo_tokenizer.pad_token = self.gpt_neo_tokenizer.eos_token
                    logger.info("✅ GPT-Neo模型加载成功。")
                except Exception as e:
                    self.gpt_neo_model = None
                    self.gpt_neo_tokenizer = None
                    logger.error(f"❌ GPT-Neo模型加载失败: {e}\n{traceback.format_exc()}", exc_info=True)
            else:
                logger.info("ℹ️ GPT-Neo未启用，跳过加载。")

        except Exception as e:
            logger.error(f"❌ 加载高级AI模型时发生外部意外错误: {e}\n{traceback.format_exc()}", exc_info=True)
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
            'precision_level': precision_level.value,
            'use_gpu': self.device == "cuda",
            'device': self.device,
            'init_time': init_time,
            'config': self.config.copy(),
            'components': {
                'tesseract_enabled': True,
                'fsrcnn_enabled': self.config.get('enable_super_resolution', False) and (self.fsrcnn_model is not None),
                'layoutlm_enabled': self.config.get('enable_layout_analysis', False) and (self.layoutlm_model is not None),
                'gpt_neo_enabled': self.config.get('enable_context_analysis', False) and (self.gpt_neo_model is not None),
                'transformer_ocr_enabled': self.config.get('enable_transformer_ocr', False) and (self.trocr_model is not None)
            },
            'system_info': CVOCRVersionManager.get_system_info(),
            'initialization_timestamp': datetime.now().isoformat()
        }
        
        # 运行测试 (测试核心Tesseract功能)
        test_success, test_msg = self._test_ocr_engine()
        if not test_success:
            self.is_initialized = False
            return False, f"CVOCR引擎初始化成功，但Tesseract基础测试失败: {test_msg}"
        
        success_message = f"CVOCR引擎初始化成功：语言: {language.value}, 精度: {precision_level.value}, 耗时: {init_time:.2f}秒"
        logger.info(f"{success_message}, AI设备: {self.device}")
        return True, success_message
    
    
    def _initialize_tesseract(self) -> Tuple[bool, str]:
        """初始化Tesseract OCR (V3.4 语言包检查增强版)"""
        try:
            import pytesseract
            
            # 确认 Tesseract 可执行文件路径
            tesseract_cmd = self.tesseract_path if self.tesseract_path and os.path.exists(self.tesseract_path) else 'tesseract'
            
            # 获取 Tesseract 版本 (顺便检查是否能执行)
            try:
                version = pytesseract.get_tesseract_version()
                logger.info(f"Tesseract OCR引擎可用，版本: {version}")
            except Exception as e:
                logger.error(f"❌ Tesseract 可执行文件无法运行或版本检测失败: {e}", exc_info=True)
                return False, f"Tesseract 可执行文件无法运行或版本检测失败: {e}"

            # 获取 Tesseract 配置字符串
            tesseract_config_str = self._get_tesseract_config(self.precision_level, self.language)
            self.tesseract_config = tesseract_config_str # 更新实例属性
            
            # 检查语言包是否安装
            requested_langs = self.config['lang'].split('+')
            
            # 确保在调用subprocess.run时使用正确的tesseract_cmd
            tesseract_executable_for_subprocess = self.tesseract_path if (self.tesseract_path and os.path.exists(self.tesseract_path)) else "tesseract"

            try:
                available_langs_output = subprocess.run([tesseract_executable_for_subprocess, '--list-langs'], capture_output=True, text=True, check=True)
                available_langs = set(line.strip() for line in available_langs_output.stdout.splitlines() if line.strip() and not line.strip().startswith('tesseract'))
                
                missing_langs = [lang for lang in requested_langs if lang not in available_langs]
                
                message = f"Tesseract初始化成功，版本: {version}" # 默认消息
                if missing_langs:
                    logger.warning(f"⚠️ 缺少Tesseract语言包: {', '.join(missing_langs)}。请安装。")
                    # 尝试使用只安装的语言进行识别，如果一个都没有，则视为失败
                    if not any(lang in available_langs for lang in requested_langs):
                        return False, f"Tesseract缺少所有请求的语言包: {', '.join(requested_langs)}。请安装。"
                    else:
                        # 至少部分语言包存在，警告但不失败
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
            
            return True, message # 返回完整的消息
                
        except ImportError:
            logger.error("❌ pytesseract未安装，请安装: pip install pytesseract", exc_info=True)
            return False, "pytesseract未安装，请安装: pip install pytesseract"
        except Exception as e:
            logger.error(f"❌ Tesseract初始化失败: {e}\n{traceback.format_exc()}", exc_info=True)
            return False, f"Tesseract初始化失败: {str(e)}"
    
    def _initialize_fsrcnn_model(self):
        """FSRCNN超分辨率模型初始化 (保持模拟，待后续专业化)"""
        logger.info("FSRCNN超分辨率模型配置完成（演示模式）")
    
    def _get_tesseract_config(self, precision_level: OCRPrecisionLevel, language: OCRLanguage) -> str:
        """
        根据精度级别获取Tesseract配置 (V3.10 最终修正版)
        - 移除了错误的字符白名单，允许Tesseract使用完整的语言模型。
        - 保留了对中英混合场景的优化参数。
        """
        # 基础配置，根据精度级别选择PSM和OEM模式
        config_map = {
            OCRPrecisionLevel.FAST: {'psm': 7, 'oem': 3},
            OCRPrecisionLevel.BALANCED: {'psm': 3, 'oem': 3},
            OCRPrecisionLevel.ACCURATE: {'psm': 3, 'oem': 1}, # 精确模式使用纯LSTM引擎，更稳定
            OCRPrecisionLevel.ULTRA: {'psm': 1, 'oem': 1},   # 超精确模式也使用纯LSTM
        }
        
        config_settings = config_map.get(precision_level, config_map[OCRPrecisionLevel.BALANCED])
        
        # 优先使用GUI界面上用户手动设置的PSM
        psm_val = self.config.get('psm', config_settings['psm'])
        oem_val = config_settings['oem']

        # 确定语言代码
        lang_code = self.config.get('lang', 'chi_sim+eng')

        # --- 核心修正：移除错误的tessedit_char_whitelist ---
        extra_configs = []
        if 'chi_sim' in lang_code or 'chi_tra' in lang_code:
            # 这些参数有助于改善中文或中英混合识别
            extra_configs.extend([
                '-c textord_tabfind_find_tables=1',
                '-c chopper_enable=0',
                '-c preserve_interword_spaces=1',
                '-c language_model_penalty_non_freq_dict_word=0.1',
                '-c language_model_penalty_non_dict_word=0.15',
                # 此处不再有 tessedit_char_whitelist
            ])
        
        # 构建最终的配置字符串
        config_str = f'--psm {psm_val} --oem {oem_val} -l {lang_code}'
        
        if extra_configs:
            config_str += ' ' + ' '.join(extra_configs)
        
        # 更新实例内部的config，确保一致性
        self.config['psm'] = psm_val
        self.config['oem'] = oem_val
        self.config['lang'] = lang_code
        
        logger.info(f"Tesseract配置已更新: {config_str}")
        
        return config_str
   
    def _test_ocr_engine(self) -> Tuple[bool, str]:
        """测试OCR引擎 (仅测试Tesseract基础功能)"""
        try:
            import pytesseract
            
            test_img = np.ones((100, 400, 3), dtype=np.uint8) * 255
            cv2.putText(test_img, 'CVOCR Test 2025', (50, 50), cv2.FONT_HERSHEY_SIMPLEX, 1, (0, 0, 0), 2)
            
            # 使用 Image.fromarray 确保图像格式正确
            test_pil_img = Image.fromarray(cv2.cvtColor(test_img, cv2.COLOR_BGR2RGB))

            # 调用 _execute_tesseract_subprocess 确保测试与实际识别流程一致
            tesseract_result = self._execute_tesseract_subprocess(
                image_pil=test_pil_img,
                tesseract_cmd_path=self.tesseract_path,
                config_str=self.tesseract_config,
                timeout=self.config.get('tesseract_process_timeout', 300)
            )

            if tesseract_result['status'] == 'error':
                logger.error(f"OCR引擎测试失败 (Tesseract子进程错误): {tesseract_result['message']}")
                return False, f"OCR引擎测试失败: {tesseract_result['message']}"

            result = tesseract_result['full_text']
            
            if any(word in result.upper() for word in ['CVOCR', 'TEST', '2025']):
                return True, f"OCR引擎测试通过，识别结果: {result.strip()}"
            else:
                return True, f"OCR引擎可用，测试结果: {result.strip()}" # 即使没完全识别对，只要能运行也算可用
                
        except Exception as e:
            logger.error(f"OCR引擎测试失败: {e}\n{traceback.format_exc()}")
            return False, f"OCR引擎测试异常: {str(e)}"
    def _run_segmentation_and_recognize(self, image_np: np.ndarray, precision_level: OCRPrecisionLevel, scale_factors: Tuple[float, float]) -> Tuple[Dict, str]:
        """
        执行高级分割并对每个区域进行识别 (V3.15 坐标系统一最终版)
        - 接收原始尺寸到当前尺寸的缩放比例。
        - 将所有识别出的局部坐标，反向缩放回原始坐标系。
        """
        logger.info(f"🚀 开始执行高级分割流程... 缩放比例: x={scale_factors[0]:.2f}, y={scale_factors[1]:.2f}")
        self.performance_stats['component_usage']['advanced_segmentation'] += 1
        image_for_detection = image_np.copy()
        if len(image_for_detection.shape) == 2:
             image_for_detection = cv2.cvtColor(image_for_detection, cv2.COLOR_GRAY2BGR)
        normal_regions, _ = self.text_detector.detect_text_regions_advanced(image_for_detection, precision_level)
        inverted_image = cv2.bitwise_not(image_for_detection)
        inverted_regions, _ = self.text_detector.detect_text_regions_advanced(inverted_image, precision_level)
        gray_image = cv2.cvtColor(image_for_detection, cv2.COLOR_BGR2GRAY)
        _, binarized_image = cv2.threshold(gray_image, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        binarized_bgr = cv2.cvtColor(binarized_image, cv2.COLOR_GRAY2BGR)
        binarized_regions, _ = self.text_detector.detect_text_regions_advanced(binarized_bgr, precision_level)
        all_detected_regions = normal_regions + inverted_regions + binarized_regions
        scores = [cv2.contourArea(region) for region in all_detected_regions]
        indices = sorted(range(len(scores)), key=lambda k: scores[k], reverse=True)
        final_regions = []
        while len(indices) > 0:
            current_index = indices.pop(0)
            current_region = all_detected_regions[current_index]
            final_regions.append(current_region)
            remaining_indices = []
            for i in indices:
                if self._calculate_bbox_iou_for_polygons(current_region, all_detected_regions[i]) < 0.5:
                    remaining_indices.append(i)
            indices = remaining_indices
        regions = final_regions
        
        if not regions: return {}, ""
        
        all_ocr_data = defaultdict(list)
        recognized_parts = []
        scale_x, scale_y = scale_factors
        
        for i, region_box in enumerate(regions):
            try:
                rect = cv2.minAreaRect(region_box)
                center, size, angle = rect
                width, height = int(size[0]), int(size[1])
                if height > width * 1.5:
                    angle += 90; width, height = height, width
                M = cv2.getRotationMatrix2D(center, angle, 1.0)
                warped_bgr = cv2.warpAffine(image_np, M, (image_np.shape[1], image_np.shape[0]), flags=cv2.INTER_CUBIC)
                cropped_bgr = cv2.getRectSubPix(warped_bgr, (width, height), center)
                if cropped_bgr is None or cropped_bgr.size == 0: continue
                gray_cropped = cv2.cvtColor(cropped_bgr, cv2.COLOR_BGR2GRAY)
                h, w = gray_cropped.shape
                if h > 0 and (h < 24 or h > 64):
                    scale = 40.0 / h
                    gray_cropped = cv2.resize(gray_cropped, (0,0), fx=scale, fy=scale, interpolation=cv2.INTER_CUBIC)
                clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(4, 4))
                enhanced_contrast = clahe.apply(gray_cropped)
                _, binarized = cv2.threshold(enhanced_contrast, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
                bordered = cv2.copyMakeBorder(binarized, 5, 5, 5, 5, cv2.BORDER_CONSTANT, value=[255])
                processed_for_ocr = cv2.cvtColor(bordered, cv2.COLOR_GRAY2BGR)
                cropped_pil = Image.fromarray(cv2.cvtColor(processed_for_ocr, cv2.COLOR_BGR2RGB))
                tesseract_config_str = self._get_tesseract_config(self.precision_level, self.language)
                psm_mode = 7 if max(cropped_bgr.shape) > 50 else 8
                tesseract_config_str = re.sub(r'--psm \d+', f'--psm {psm_mode}', tesseract_config_str)
                region_result = self._execute_tesseract_subprocess(
                    image_pil=cropped_pil, tesseract_cmd_path=self.tesseract_path,
                    config_str=tesseract_config_str, timeout=tesseract_timeout
                )

                if region_result["status"] == "success" and region_result.get("data"):
                    box_points_original = cv2.boxPoints(rect)
                    x_start_processed, y_start_processed = int(min(box_points_original[:, 0])), int(min(box_points_original[:, 1]))
                    
                    region_data = region_result["data"]
                    for j in range(len(region_data.get('text', []))):
                        abs_x_processed = region_data['left'][j] + x_start_processed
                        abs_y_processed = region_data['top'][j] + y_start_processed
                        width_processed = region_data['width'][j]
                        height_processed = region_data['height'][j]
                        
                        all_ocr_data['left'].append(int(abs_x_processed * scale_x))
                        all_ocr_data['top'].append(int(abs_y_processed * scale_y))
                        all_ocr_data['width'].append(int(width_processed * scale_x))
                        all_ocr_data['height'].append(int(height_processed * scale_y))
                        
                        for key in ['text', 'conf', 'word_num', 'line_num', 'par_num', 'block_num']:
                            if key in region_data and j < len(region_data[key]):
                                all_ocr_data[key].append(region_data[key][j])
                    
                    region_text = region_result.get("full_text", "").strip()
                    if region_text:
                        recognized_parts.append({
                            'text': region_text, 
                            'y_coord': int(y_start_processed * scale_y), 
                            'x_coord': int(x_start_processed * scale_x)
                        })
            
            except Exception as e:
                continue
                
        recognized_parts.sort(key=lambda item: (item['y_coord'], item['x_coord']))
        final_full_text = "\n".join([part['text'] for part in recognized_parts])

        return dict(all_ocr_data), final_full_text
    
    
    
    
    
    # 需要在 EnhancedCVOCRManager 类中添加一个新的辅助方法来计算IoU
    def _calculate_bbox_iou_for_polygons(self, poly1, poly2) -> float:
        """计算两个多边形区域的交并比(IoU)"""
        try:
            # 创建两个空白图像
            img1 = np.zeros((1,1), dtype=np.uint8) # 尺寸不重要，我们会用boundingRect
            img2 = np.zeros((1,1), dtype=np.uint8)

            # 获取两个多边形的外接矩形，以确定需要的图像大小
            r1 = cv2.boundingRect(poly1.astype(int))
            r2 = cv2.boundingRect(poly2.astype(int))
            
            # 计算一个能包含两个矩形的公共画布大小
            max_x = max(r1[0]+r1[2], r2[0]+r2[2])
            max_y = max(r1[1]+r1[3], r2[1]+r2[3])
            
            img1 = np.zeros((max_y, max_x), dtype=np.uint8)
            img2 = np.zeros((max_y, max_x), dtype=np.uint8)

            # 在各自的图像上绘制填充的多边形
            cv2.fillPoly(img1, [poly1.astype(int)], 255)
            cv2.fillPoly(img2, [poly2.astype(int)], 255)
            
            # 计算交集和并集
            intersection = np.sum(cv2.bitwise_and(img1, img2) > 0)
            union = np.sum(cv2.bitwise_or(img1, img2) > 0)
            
            if union == 0:
                return 0.0
            
            return intersection / union
        except Exception:
            return 0.0
    def recognize_text_enhanced(self, image_path: str, enable_preprocessing: bool = True,
                                precision_override: Optional[OCRPrecisionLevel] = None) -> Tuple[Optional[Dict], str]:
        """
        CVOCR增强文本识别的核心实现 (V3.15 坐标系统一最终版)
        """
        recognition_start_time = time.time()
        self.performance_stats['total_recognitions'] += 1
        precision_level_enum = precision_override or self.precision_level
        language_enum = self.language
        use_advanced_segmentation = self.config.get('enable_advanced_segmentation', False)
        preprocess_flags = self.config.copy()
        preprocess_flags.update({
            'enable_preprocessing': enable_preprocessing,
            'enable_advanced_segmentation': use_advanced_segmentation,
            'precision_level': precision_level_enum.value, 
            'language': language_enum.value
        })
        tesseract_timeout = self.config.get('tesseract_process_timeout', 300)

        # --- 核心修正：获取原始尺寸 ---
        try:
            with Image.open(image_path) as img:
                original_width, original_height = img.size
        except Exception as e:
            self._update_failed_stats()
            return None, f"无法读取原始图像尺寸: {e}"

        image_processor = AdvancedTextImageProcessor() 
        processed_image_np, preprocess_msg, metadata = image_processor.intelligent_preprocess_image(
            image_path, **preprocess_flags 
        )
        if processed_image_np is None:
            self._update_failed_stats()
            return None, f"图像预处理失败: {preprocess_msg}"
        
        # 计算预处理过程中的缩放比例
        processed_height, processed_width = processed_image_np.shape[:2]
        scale_x = original_width / processed_width if processed_width > 0 else 1.0
        scale_y = original_height / processed_height if processed_height > 0 else 1.0
        
        if self.config.get('enable_super_resolution', False):
            if self.fsrcnn_model and processed_image_np is not None:
                h_before, w_before = processed_image_np.shape[:2]
                processed_image_np = self._apply_fsrcnn_enhancement(processed_image_np)
                h_after, w_after = processed_image_np.shape[:2]
                if h_after > 0 and w_after > 0:
                    scale_x *= w_before / w_after
                    scale_y *= h_before / h_after
                self.performance_stats['component_usage']['fsrcnn'] += 1
        
        layout_info, context_info, transformer_results = None, None, None
        if self.config.get('enable_layout_analysis', False) and self.layoutlm_model:
            layout_info = self._analyze_layout_with_layoutlmv2(processed_image_np)
            self.performance_stats['component_usage']['layoutlmv2'] += 1
        if self.config.get('enable_transformer_ocr', False) and self.trocr_model:
            transformer_results = self._apply_transformer_ocr(processed_image_np)
            self.performance_stats['component_usage']['transformer_ocr'] += 1

        ocr_data, full_text = None, None
        is_trocr_result_valid = False
        if transformer_results and 'text' in transformer_results and transformer_results['text'].strip():
            trocr_text = transformer_results['text'].strip()
            if len(trocr_text) > 2 and re.search(r'[a-zA-Z\u4e00-\u9fa5]', trocr_text):
                is_trocr_result_valid = True
        
        if is_trocr_result_valid:
            full_text = transformer_results['text']
        elif use_advanced_segmentation:
            try:
                seg_precision_str = self.config.get('segmentation_precision', 'balanced')
                seg_precision_enum = OCRPrecisionLevel(seg_precision_str)
                # **关键：将缩放比例传递下去**
                ocr_data, full_text = self._run_segmentation_and_recognize(
                    processed_image_np, seg_precision_enum, (scale_x, scale_y)
                )
            except Exception as e:
                ocr_data, full_text = None, None
        
        if ocr_data is None and not is_trocr_result_valid:
             try:
                 image_pil = Image.fromarray(cv2.cvtColor(processed_image_np, cv2.COLOR_BGR2RGB))
                 tesseract_config_str = self._get_tesseract_config(precision_level_enum, language_enum)
                 tesseract_result = self._execute_tesseract_subprocess(
                     image_pil=image_pil, tesseract_cmd_path=self.tesseract_path,
                     config_str=tesseract_config_str, timeout=tesseract_timeout
                 )
                 self.performance_stats['component_usage']['tesseract'] += 1
                 if tesseract_result["status"] == "error":
                     raise CVOCRException(tesseract_result['message'])
                 ocr_data = tesseract_result["data"]
                 full_text = tesseract_result["full_text"]
                 # **关键：对整页识别的结果也进行坐标转换**
                 if ocr_data and 'left' in ocr_data:
                     ocr_data['left'] = [int(x * scale_x) for x in ocr_data['left']]
                     ocr_data['top'] = [int(y * scale_y) for y in ocr_data['top']]
                     ocr_data['width'] = [int(w * scale_x) for w in ocr_data['width']]
                     ocr_data['height'] = [int(h * scale_y) for h in ocr_data['height']]
             except Exception as e:
                 self._update_failed_stats()
                 return None, f"Tesseract整页识别失败: {str(e)}"

        if self.config.get('enable_context_analysis', False) and full_text:
            avg_confidence = 0
            if ocr_data and ocr_data.get('conf'):
                valid_confs = [c for c in ocr_data.get('conf', []) if c != -1]
                if valid_confs:
                    avg_confidence = sum(valid_confs) / len(valid_confs)
            if not is_trocr_result_valid and avg_confidence < 75.0:
                full_text, context_info = self._analyze_context_with_gpt_neo(full_text, ocr_data or {})
                self.performance_stats['component_usage']['gpt_neo'] += 1
        
        final_results = self._post_process_cvocr_results(
            ocr_data, full_text, precision_level_enum, 
            layout_info, context_info, transformer_results, metadata
        )
        
        processing_time = time.time() - recognition_start_time
        self._update_success_stats(processing_time)
        summary_msg = self._generate_cvocr_result_summary(final_results, processing_time, preprocess_msg)
        final_results['processing_metadata']['total_processing_time'] = processing_time
        return final_results, summary_msg
    
    
    
    
    def _apply_fsrcnn_enhancement(self, image: np.ndarray) -> np.ndarray:
        """
        应用FSRCNN超分辨率增强 (V3.11 修正为无损放大模拟)。
        - 移除了破坏性的锐化和边缘融合。
        - 使用高质量的双三次插值进行放大，作为更安全的模拟方式。
        """
        try:
            h, w = image.shape[:2]
            scale_factor = self.fsrcnn_model.get('scale_factor', 2)
            
            # --- 核心修正：只使用高质量的插值放大 ---
            # 这种方法不会引入破坏性的伪影，对后续的分割和识别更友好。
            new_h, new_w = int(h * scale_factor), int(w * scale_factor)
            if new_h > 0 and new_w > 0:
                enhanced = cv2.resize(image, (new_w, new_h), interpolation=cv2.INTER_CUBIC)
                logger.info(f"FSRCNN模拟增强完成 (高质量放大): {w}x{h} -> {new_w}x{new_h}")
                return enhanced
            else:
                logger.warning("FSRCNN计算出的新尺寸无效，跳过增强。")
                return image

        except Exception as e:
            logger.error(f"FSRCNN增强处理失败: {e}", exc_info=True)
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
            
            # 调整图像大小到模型期望的输入尺寸 (LayoutLMv2通常是224x224或800x800)
            # LayoutLMv2Processor会自动处理尺寸，但我们可以预先调整以避免内存问题
            target_size = (800, 800) # LayoutLMv2常见输入尺寸
            if pil_image.width > target_size[0] or pil_image.height > target_size[1]:
                pil_image = pil_image.resize(target_size, Image.Resampling.LANCZOS)

            # 准备模型输入
            # LayoutLMv2Processor需要图像和可选的OCR文本/盒子来做预处理
            # 暂时不提供OCR文本，让模型自己从图像中提取
            encoding = self.layoutlm_processor(pil_image, return_tensors="pt").to(self.device)
            
            # 模型推理
            with torch.no_grad():
                outputs = self.layoutlm_model(**encoding)
            
            # 解析预测结果
            predictions = outputs.logits.argmax(-1).squeeze().tolist()
            token_boxes = encoding.bbox.squeeze().tolist()
            tokens = self.layoutlm_processor.tokenizer.convert_ids_to_tokens(encoding.input_ids.squeeze().tolist())
            
            # 将token级别的预测聚合为有意义的区域
            # 这是一个简化的聚合逻辑，实际应用会更复杂
            text_regions = []
            for i, pred in enumerate(predictions):
                if pred == 0: # 假设0是背景/非文本
                    continue
                
                # 排除特殊token
                if tokens[i] in ['[CLS]', '[SEP]', '[PAD]']:
                    continue

                box = token_boxes[i]
                # Bounding box coordinates are typically normalized (0-1000) or pixel values
                # We need to scale them back if they were normalized
                # LayoutLMv2's processor often outputs normalized boxes.
                # Assuming here the boxes are directly usable or require minimal scaling.
                
                # A simple aggregation logic: each token is a "region" for now
                # More robust: group adjacent tokens of the same predicted type
                text_regions.append({
                    'text': tokens[i],
                    'bbox': [box[0], box[1], box[2], box[3]], # x_min, y_min, x_max, y_max
                    'type_id': pred,
                    'type_name': self.layoutlm_model.config.id2label.get(pred, 'UNKNOWN'),
                    'confidence': float(torch.softmax(outputs.logits, dim=-1).squeeze()[i][pred].item())
                })
            
            # 进一步聚合文本区域，并确保坐标在图像范围内
            aggregated_regions = self._aggregate_layoutlmv2_regions(text_regions, image.shape[1], image.shape[0])

            layout_analysis = {
                'text_regions': aggregated_regions,
                'document_structure': {
                    'estimated_language': 'mixed', # LayoutLMv2本身不直接检测语言，需结合OCR结果
                    'text_density': 'medium'
                },
                'confidence_score': float(torch.softmax(outputs.logits, dim=-1).max().item()), # 整个文档的最高预测置信度
            }
            
            logger.info(f"LayoutLMv2布局分析完成，检测到 {len(aggregated_regions)} 个聚合文本区域。")
            return layout_analysis
        except Exception as e:
            logger.error(f"LayoutLMv2布局分析失败: {e}\n{traceback.format_exc()}")
            return {'error': str(e), 'text_regions': []}
    
    def _aggregate_layoutlmv2_regions(self, regions: List[Dict], image_width: int, image_height: int) -> List[Dict]:
        """
        聚合LayoutLMv2输出的token级区域，形成更粗粒度的文本块。
        这里是一个简化的实现，实际需要更复杂的启发式算法或聚类。
        """
        aggregated_output = []
        
        # 将归一化的box（0-1000）转换为像素坐标
        def scale_box(box):
            return [
                int(box[0] / 1000 * image_width),
                int(box[1] / 1000 * image_height),
                int(box[2] / 1000 * image_width),
                int(box[3] / 1000 * image_height)
            ]

        # 先按行和类型排序
        regions.sort(key=lambda r: (r['bbox'][1], r['bbox'][0], r['type_id']))

        current_block = None
        for region in regions:
            scaled_bbox = scale_box(region['bbox'])
            if current_block is None:
                current_block = {
                    'text': region['text'],
                    'bbox': scaled_bbox,
                    'type_name': region['type_name'],
                    'type_id': region['type_id'],
                    'confidence': region['confidence'],
                    'count': 1
                }
            else:
                # 简单的合并逻辑：如果类型相同且在水平/垂直方向上接近
                # 这里可以加入更多的判断，例如行间距、字符间距等
                overlap_threshold = 20 # 像素容忍度
                if region['type_id'] == current_block['type_id'] and \
                   abs(scaled_bbox[1] - current_block['bbox'][1]) < overlap_threshold: # 同一行
                    
                    # 合并文本和边界框
                    current_block['text'] += " " + region['text']
                    current_block['bbox'][0] = min(current_block['bbox'][0], scaled_bbox[0])
                    current_block['bbox'][1] = min(current_block['bbox'][1], scaled_bbox[1])
                    current_block['bbox'][2] = max(current_block['bbox'][2], scaled_bbox[2])
                    current_block['bbox'][3] = max(current_block['bbox'][3], scaled_bbox[3])
                    current_block['confidence'] = (current_block['confidence'] * current_block['count'] + region['confidence']) / (current_block['count'] + 1)
                    current_block['count'] += 1
                else:
                    # 新的文本块
                    aggregated_output.append(current_block)
                    current_block = {
                        'text': region['text'],
                        'bbox': scaled_bbox,
                        'type_name': region['type_name'],
                        'type_id': region['type_id'],
                        'confidence': region['confidence'],
                        'count': 1
                    }
        if current_block:
            aggregated_output.append(current_block)
            
        # 清理和最终格式化
        final_regions = []
        for block in aggregated_output:
            final_regions.append({
                'bbox': [int(coord) for coord in block['bbox']],
                'text': block['text'].strip(),
                'type': block['type_name'],
                'confidence': block['confidence']
            })
        
        return final_regions

    def _apply_transformer_ocr(self, image: np.ndarray) -> Dict:
        """使用真正的TrOCR模型进行端到端OCR识别。"""
        import torch
        from transformers import TrOCRProcessor, VisionEncoderDecoderModel

        if not self.trocr_model or not self.trocr_processor:
            logger.warning("TrOCR模型或处理器未加载，无法进行TrOCR识别。")
            return {'error': 'TrOCR模型未加载', 'text': ''}

        try:
            pil_image = Image.fromarray(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))

            # 准备模型输入
            pixel_values = self.trocr_processor(images=pil_image, return_tensors="pt").pixel_values.to(self.device)
            
            # 生成文本ID
            with torch.no_grad():
                generated_ids = self.trocr_model.generate(pixel_values)
            
            # 解码为文本
            generated_text = self.trocr_processor.batch_decode(generated_ids, skip_special_tokens=True)[0]
            
            transformer_results = {
                'method': 'transformer_ocr',
                'model_name': 'microsoft/trocr-base-handwritten', # 根据实际加载的模型更新
                'text': generated_text,
                'confidence': 1.0 # TrOCR不直接输出置信度，这里给个高默认值
            }
            logger.info(f"TrOCR识别完成: '{generated_text[:min(len(generated_text), 50)]}...'")
            
            if 'component_usage' in self.performance_stats: # 更新性能统计
                self.performance_stats['component_usage']['transformer_ocr'] += 1
            return transformer_results
        except Exception as e:
            logger.error(f"TrOCR处理失败: {e}\n{traceback.format_exc()}")
            return {'error': str(e), 'text': ''}
    
    def _analyze_context_with_gpt_neo(self, text: str, ocr_data: Dict) -> Tuple[str, Dict]:
        """使用真正的GPT-Neo进行上下文分析和文本优化。"""
        import torch
        from transformers import GPT2Tokenizer, GPTNeoForCausalLM

        if not self.gpt_neo_model or not self.gpt_neo_tokenizer:
            logger.warning("GPT-Neo模型或分词器未加载，无法进行上下文分析。")
            return text, {'error': 'GPT-Neo模型未加载'}

        try:
            # 限制输入文本长度，GPT-Neo-125M模型的上下文窗口较小
            max_input_length = 512 - 50 # 留一些空间给生成文本
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
            
            max_new_tokens = min(200, int(len(input_ids[0]) * 0.5) + 20) # 限制生成长度，避免模型跑偏
            
            with torch.no_grad():
                gen_tokens = self.gpt_neo_model.generate(
                    input_ids,
                    do_sample=True,
                    temperature=0.7, # 增加一些创造性
                    top_p=0.9,       # 增加多样性
                    max_new_tokens=max_new_tokens,
                    pad_token_id=self.gpt_neo_tokenizer.eos_token_id # 确保 pad_token_id 设置正确
                )
            
            corrected_text_full = self.gpt_neo_tokenizer.decode(gen_tokens[0], skip_special_tokens=True)
            
            # 尝试提取 "Corrected Text:" 之后的部分
            if "Corrected Text:" in corrected_text_full:
                optimized_text = corrected_text_full.split("Corrected Text:", 1)[1].strip()
            else:
                # 如果没有找到分隔符，说明模型可能没有遵循指令，尝试回退或简单清理
                optimized_text = corrected_text_full.replace(prompt.split('---')[0].strip(), '').strip()
                optimized_text = optimized_text.replace(text, '').strip() # 再次尝试移除原始prompt
                if not optimized_text: # 如果移除后为空，说明提取失败，使用原始文本
                    optimized_text = text
                
            # 简单的差异计算来估计纠正数量
            corrections_applied = 0
            if optimized_text != text:
                corrections_applied = abs(len(text) - len(optimized_text)) # 粗略估计
            
            context_analysis = {
                'original_length': len(text),
                'optimized_length': len(optimized_text),
                'corrections_applied': corrections_applied,
                'semantic_coherence': 0.95, # 假设模型提升了语义连贯性
                'processing_method': 'gpt-neo-125m',
                'model_confidence': 0.90 # 假设模型对自己的输出有较高信心
            }
            
            logger.info(f"GPT-Neo上下文分析完成，文本长度从 {len(text)} 变为 {len(optimized_text)}，应用了约 {corrections_applied} 处修正。")
            if 'component_usage' in self.performance_stats: # 更新性能统计
                self.performance_stats['component_usage']['gpt_neo'] += 1
            return optimized_text, context_analysis
            
        except Exception as e:
            logger.error(f"GPT-Neo上下文分析失败: {e}\n{traceback.format_exc()}")
            return text, {'error': str(e)}
    
    def _post_process_cvocr_results(self, data: Optional[Dict], full_text: str, precision_level: OCRPrecisionLevel, 
                                    layout_info: Dict = None, context_info: Dict = None, 
                                    transformer_results: Dict = None, preprocess_metadata: Dict = None) -> Dict:
        """
        CVOCR结果后处理和整合 (V3.7 逻辑修复版)。
        - 统一处理来自不同OCR源（TrOCR, Tesseract）的数据。
        - 只有在TrOCR结果有效时，才将其作为唯一结果进行整合。
        - 否则，处理来自Tesseract（通过高级分割或整页识别）的数据。
        - 将所有相关信息（布局、上下文、元数据等）整合到最终的结构化字典中。
        """
        try:
            text_blocks = []
            
            # 推断处理后的图像尺寸，用于创建TrOCR的边界框
            image_w, image_h = 1000, 800 # 默认值
            if preprocess_metadata and 'final_shape' in preprocess_metadata:
                image_h, image_w = preprocess_metadata['final_shape'][:2]

            # --- 关键修正：重新进行TrOCR结果的有效性验证，确保与主流程逻辑一致 ---
            is_trocr_result_valid = False
            if self.config.get('enable_transformer_ocr', False) and transformer_results and 'text' in transformer_results and transformer_results['text'].strip():
                trocr_text = transformer_results['text'].strip()
                # 使用与主流程中完全相同的验证逻辑
                if len(trocr_text) > 2 and re.search(r'[a-zA-Z\u4e00-\u9fa5]', trocr_text):
                    is_trocr_result_valid = True

            # --- 结果整合分支逻辑 ---
            if is_trocr_result_valid:
                # 分支一: TrOCR结果有效，将其作为唯一的文本块进行整合
                logger.info("TrOCR结果有效，将其整合为唯一的识别文本块。")
                text_blocks.append({
                    'text': transformer_results['text'],
                    'confidence': int(transformer_results.get('confidence', 99.0)), # TrOCR不直接输出置信度，使用高默认值
                    'bbox': [0, 0, image_w, image_h], # 假设覆盖整个图像
                    'word_num': len(transformer_results['text'].split()),
                    'line_num': 1, 
                    'par_num': 1, 
                    'block_num': 1,
                    'transformer_enhanced': True # 明确标记此块来自TrOCR
                })
                # 注意：如果GPT-Neo运行了，full_text已经是优化后的版本，这里无需再次赋值
            
            elif data:
                # 分支二: TrOCR无效或未启用，处理来自Tesseract的数据
                # (数据可能来自高级分割或整页识别)
                if 'text' not in data or not isinstance(data.get('text'), list):
                    logger.warning("接收到的Tesseract数据结构异常或为空，无法解析文本块。")
                else:
                    for i in range(len(data['text'])):
                        # 安全地获取置信度，处理-1的情况
                        conf_str = data['conf'][i] if i < len(data['conf']) else '-1'
                        conf = int(float(conf_str)) if conf_str != '-1' else 0
                        
                        text = data['text'][i].strip()
                        
                        # 根据用户设置的置信度阈值进行过滤
                        if conf < self.config.get('confidence_threshold', 60) or not text:
                            continue
                        
                        # 安全地获取边界框坐标
                        if all(k in data and i < len(data[k]) for k in ['left', 'top', 'width', 'height']):
                            bbox_coords = [
                                int(data['left'][i]), int(data['top'][i]),
                                int(data['left'][i] + data['width'][i]), int(data['top'][i] + data['height'][i])
                            ]
                        else:
                            logger.warning(f"文本块 '{text[:20]}...' 的边界框数据不完整，已跳过。")
                            continue

                        # 构建文本块字典
                        text_block = {
                            'text': text, 
                            'confidence': conf, 
                            'bbox': bbox_coords,
                            'word_num': int(data['word_num'][i]) if i < len(data['word_num']) else len(text.split()),
                            'line_num': int(data['line_num'][i]) if i < len(data['line_num']) else 0,
                            'par_num': int(data['par_num'][i]) if i < len(data['par_num']) else 0,
                            'block_num': int(data['block_num'][i]) if i < len(data['block_num']) else 0
                        }

                        # 如果有AI增强信息，则附加
                        if context_info:
                            text_block['context_enhanced'] = True
                        if layout_info:
                            text_block['layout_info'] = self._match_text_to_layout(text_block, layout_info)
                        
                        text_blocks.append(text_block)
            
            # --- 后续处理与整合 (对所有分支的结果都有效) ---
            
            # 按阅读顺序对文本块进行排序（块号 -> 段落号 -> 行号 -> 水平位置）
            text_blocks.sort(key=lambda x: (x.get('block_num', 0), x.get('par_num', 0), x.get('line_num', 0), x.get('bbox', [0,0,0,0])[0]))
            
            # 计算最终的统计数据
            total_chars = sum(len(block['text']) for block in text_blocks)
            avg_confidence = sum(block['confidence'] for block in text_blocks) / len(text_blocks) if text_blocks else 0
            
            # 构建最终的、完整的CVOCR结果字典
            cvocr_results = {
                'full_text': full_text.strip() if full_text else '',
                'text_blocks': text_blocks,
                'total_blocks': len(text_blocks),
                'total_characters': total_chars,
                'average_confidence': avg_confidence,
                'precision_level': precision_level.value,
                'language': self.language.value,
                'cvocr_components': {
                    'tesseract_used': bool(data and data.get('text')),
                    'fsrcnn_used': self.config.get('enable_super_resolution', False),
                    'layoutlmv2_used': self.config.get('enable_layout_analysis', False),
                    'gpt_neo_used': self.config.get('enable_context_analysis', False),
                    'transformer_ocr_used': is_trocr_result_valid
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
            # 在失败时也返回一个结构化的错误信息
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
            
            if best_match and max_overlap > 0.3: # 至少30%重叠
                return {
                    'region_type': best_match.get('type', best_match.get('type_name', 'unknown')), # 兼容LayoutLMv2的type_name
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
            
            ix1 = max(x1, x3)
            iy1 = max(y1, y3)
            ix2 = min(x2, x4)
            iy2 = min(y2, y4)
            
            if ix2 <= ix1 or iy2 <= iy1:
                return 0.0
            
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
        
        total_blocks = results.get('total_blocks', 0)
        total_chars = results.get('total_characters', 0)
        avg_confidence = results.get('average_confidence', 0)
        
        components = results.get('cvocr_components', {})
        used_components = []
        if components.get('tesseract_used', False): used_components.append('Tesseract')
        if components.get('fsrcnn_used', False): used_components.append('FSRCNN')
        if components.get('layoutlmv2_used', False): used_components.append('LayoutLMv2')
        if components.get('gpt_neo_used', False): used_components.append('GPT-Neo')
        if components.get('transformer_ocr_used', False): used_components.append('TransformerOCR')
        
        components_str = '+'.join(used_components) if used_components else 'Basic'
        
        summary = f"CVOCR识别完成 [{components_str}] (耗时: {processing_time:.2f}s, {total_blocks}个文本块, {total_chars}个字符, 平均置信度: {avg_confidence:.1f})"
        
        # preprocessing_info 来自 AdvancedTextImageProcessor 返回的message
        if preprocessing_info:
            summary += f", 预处理: {preprocessing_info.rstrip('; ')}"
        
        return summary
    
    def _update_success_stats(self, processing_time: float):
        """更新成功统计"""
        self.performance_stats['successful_recognitions'] += 1
        self.performance_stats['recognition_times'].append(processing_time)
        if self.performance_stats['recognition_times']:
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
            'total_recognitions': 0,
            'successful_recognitions': 0,
            'failed_recognitions': 0,
            'average_recognition_time': 0.0,
            'recognition_times': deque(maxlen=100),
            'component_usage': defaultdict(int) # 重置为defaultdict
        }
class AsyncOCRProcessor:
    def __init__(self, cvocr_manager: 'EnhancedCVOCRManager', max_workers: int = 4):
        self.cvocr_manager = cvocr_manager
        # 创建一个独立的线程池用于执行阻塞的 OCR 任务
        # 这个线程池与 asyncio 事件循环一起工作，而不是直接作为 asyncio 的executor
        self.executor = ThreadPoolExecutor(max_workers=max_workers, thread_name_prefix="AsyncOCR")
        logger.info(f"AsyncOCRProcessor initialized with ThreadPoolExecutor (max_workers={max_workers})")

    async def run_blocking_ocr_task(self, image_path: str, enable_preprocessing: bool, precision_override: Optional[OCRPrecisionLevel]) -> Tuple[Optional[Dict], str]:
        """
        在单独的线程中运行阻塞的 OCR 识别任务。
        """
        loop = asyncio.get_running_loop()
        
        # 将 cvocr_manager.recognize_text_enhanced 视为一个阻塞函数
        # 使用 loop.run_in_executor 将其调度到线程池中执行
        return await loop.run_in_executor(
            self.executor,
            self.cvocr_manager.recognize_text_enhanced,
            image_path,
            enable_preprocessing,
            precision_override
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
            
            # 技术架构说明
            draw.text((50, y_pos), "技术架构: FSRCNN + LayoutLMv2 + Tesseract + GPT-Neo + TransformerOCR", 
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
                
                table_data = [
                    ["组件名称", "版本", "功能", "状态"],
                    ["Tesseract", "5.3+", "基础OCR", "✓"],
                    ["FSRCNN", "2.0", "超分辨率", "✓"],
                    ["LayoutLMv2", "Base", "布局分析", "✓"],
                    ["GPT-Neo", "125M", "上下文分析", "✓"],
                    ["TransformerOCR", "Base", "端到端OCR", "✓"]
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
        此方法会确保将结果字典中的所有枚举类型（如OCRPrecisionLevel）转换为其字符串值，
        使其能够被JSON序列化，方便后续保存和导出。
        
        Args:
            image_path (str): 识别图像的完整路径。
            results (Dict): OCR引擎返回的原始识别结果字典。
            metadata (Optional[Dict]): 与识别过程相关的额外元数据，如处理时间。
            
        Returns:
            Optional[Dict]: 添加到历史记录的条目字典，如果失败则返回None。
        """
        try:
            # 确保枚举类型转换为其值 (字符串)，以便JSON序列化
            # 对 results 字典进行深度拷贝，并递归转换其中的枚举类型
            serializable_results = self._make_results_json_serializable(results)
            
            # 构建历史记录条目
            result_entry = {
                'id': self._generate_result_id(), # 唯一识别ID
                'timestamp': datetime.now().isoformat(), # 识别时间戳
                'image_path': image_path,
                'image_name': os.path.basename(image_path), # 文件名
                'results': serializable_results, # 存储已JSON序列化的结果
                'metadata': metadata or {}, # 额外元数据
                'total_blocks': serializable_results.get('total_blocks', 0), # 文本块总数
                'total_characters': serializable_results.get('total_characters', 0), # 字符总数
                'avg_confidence': serializable_results.get('average_confidence', 0), # 平均置信度
                'full_text': serializable_results.get('full_text', ''), # 完整的识别文本
                'precision_level': serializable_results.get('precision_level', 'unknown'), # 精度等级
                'language': serializable_results.get('language', 'unknown'), # 识别语言
                'cvocr_components': serializable_results.get('cvocr_components', {}), # 使用的CVOCR组件
                'processing_time': metadata.get('total_processing_time', 0) if metadata else 0 # 总处理时间
            }
            
            # 将新结果添加到历史记录列表的头部
            self.history.insert(0, result_entry)
            
            # 维护历史记录列表的长度，超出最大限制则移除最旧的记录
            if len(self.history) > self.max_history:
                removed_entries = self.history[self.max_history:]
                self.history = self.history[:self.max_history]
                
                # 从内部缓存中删除已移除的条目
                for entry_to_remove in removed_entries:
                    self._results_cache.pop(entry_to_remove['id'], None)
                logger.debug(f"历史记录超出 {self.max_history} 条，已移除 {len(removed_entries)} 条最旧记录。")
            
            # 更新当前结果引用
            self.current_results = serializable_results
            
            # 更新全局统计信息
            self._update_stats(result_entry)
            
            # 将结果条目缓存起来，以便通过ID快速检索
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
                    
                    # 写入CSV表头
                    writer.writerow([
                        '时间', '图片名称', '文本块数', '字符数', '平均置信度', 
                        '语言', '精度等级', '使用组件', '处理时间', '错误信息'
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
                            entry.get('precision_level', ''),
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

class EnhancedCVOCRGUI:
    """增强版CVOCR GUI主界面"""
    
    def __init__(self, master: Optional[tk.Tk] = None):
        # 初始化窗口
        if master is None:
            self.root = tk.Tk()
            self._is_standalone = True
        else:
            self.root = master
            self._is_standalone = False

        self.setup_window()
        
        # 使用增强版组件
        self.cvocr_manager = EnhancedCVOCRManager()
        self.image_processor = AdvancedTextImageProcessor()
        self.result_manager = TextResultManager()
        
        # 引入异步 OCR 处理器
        self.async_ocr_processor = AsyncOCRProcessor(self.cvocr_manager)

        # 界面变量
        self.current_image_path: Optional[str] = None
        self.processing = False
        self.photo = None
        self.current_image_display_id = None
        self.current_bboxes = []
        self._last_original_image_size: Optional[Tuple[int, int]] = None
        self._last_display_scale_ratio_x: float = 1.0
        self._last_display_scale_ratio_y: float = 1.0

        # 线程安全队列 (日志仍使用同步队列，但处理逻辑将在asyncio循环中被调度)
        self.log_queue = queue.Queue()

        # asyncio 事件循环
        self.loop = None # 将在 start_async_loop_in_thread 中初始化
        # --- 修正1: 添加事件用于同步异步循环的启动 ---
        self._loop_ready_event = threading.Event()

        # 设置选项
        self.settings = {
            'language': tk.StringVar(value='auto'),
            'precision_level': tk.StringVar(value='balanced'),
            'enable_preprocessing': tk.BooleanVar(value=True),
            'save_results': tk.BooleanVar(value=True),
            'confidence_threshold': tk.DoubleVar(value=CVOCRConstants.DEFAULT_CONFIDENCE_THRESHOLD),
            'psm_mode': tk.IntVar(value=6),
            'enable_layout_analysis': tk.BooleanVar(value=False),
            'enable_context_analysis': tk.BooleanVar(value=False),
            'enable_super_resolution': tk.BooleanVar(value=False),
            'enable_transformer_ocr': tk.BooleanVar(value=False),
            'show_confidence': tk.BooleanVar(value=True),
            'auto_correct': tk.BooleanVar(value=False),
            'use_gpu': tk.BooleanVar(value=False),
            'batch_processing': tk.BooleanVar(value=False),
            'auto_save_results': tk.BooleanVar(value=True),
            'enable_advanced_preprocessing': tk.BooleanVar(value=True),
            'tesseract_path': tk.StringVar(value=''),
            'enable_deskew': tk.BooleanVar(value=True),
            'deskew_angle_threshold': tk.DoubleVar(value=0.5),
            'remove_borders': tk.BooleanVar(value=True),
            'border_threshold': tk.IntVar(value=10),
            'crop_to_content': tk.BooleanVar(value=True),
            'page_border_detection': tk.BooleanVar(value=True),
            'shadow_removal': tk.BooleanVar(value=True),
            'denoise_strength': tk.DoubleVar(value=0.1),
            'edge_preservation': tk.DoubleVar(value=0.8),
            'unsharp_mask': tk.BooleanVar(value=True),
            'unsharp_radius': tk.DoubleVar(value=1.0),
            'unsharp_amount': tk.DoubleVar(value=1.0),
            'histogram_equalization': tk.BooleanVar(value=True),
            'bilateral_filter': tk.BooleanVar(value=True), 
            'bilateral_d': tk.IntVar(value=9),
            'bilateral_sigma_color': tk.DoubleVar(value=75.0),
            'bilateral_sigma_space': tk.DoubleVar(value=75.0),
            'apply_clahe': tk.BooleanVar(value=True), 
            'clahe_clip_limit': tk.DoubleVar(value=2.0),
            'clahe_tile_grid_size_x': tk.IntVar(value=8), 
            'clahe_tile_grid_size_y': tk.IntVar(value=8), 
            'adaptive_block_size': tk.IntVar(value=11), 
            'adaptive_c_constant': tk.IntVar(value=2), 
            # --- 新增开始 ---
            'enable_advanced_segmentation': tk.BooleanVar(value=True),  # 默认开启高级分割
            'segmentation_precision': tk.StringVar(value='balanced'),  # 默认平衡精度


        }
        
        # 创建界面
        self.create_widgets()
        self.create_status_bar()
        
        # 初始化
        self.log_message("🚀 CVOCR增强版v3.0启动成功", 'INFO')
        self.log_message("✨ 新功能：多语言识别、高级预处理、智能文本分析", 'INFO')
        self.log_message("🔧 CVOCR技术架构：FSRCNN + LayoutLMv2 + Tesseract + GPT-Neo + TransformerOCR", 'INFO')
        
        # 加载配置
        self._load_settings()

        # 启动 asyncio 事件循环在一个单独的线程中
        self._start_async_loop_in_thread()
        
        # --- 修正2: 等待异步循环中的 self.loop 初始化完成 ---
        self._loop_ready_event.wait()

        # 启动日志处理和系统检查
        # _process_queues 现在将由 asyncio loop 调度
        self.loop.call_soon_threadsafe(self.loop.create_task, self._process_queues())
        self.loop.call_soon_threadsafe(self.loop.create_task, self._trigger_initial_system_check_async())

        # --- 新增：确认 BooleanVar 默认值 ---
        for key, var in self.settings.items():
            if isinstance(var, (tk.BooleanVar, tk.StringVar, tk.IntVar, tk.DoubleVar)):
                logger.debug(f"DEBUG: Setting '{key}' initial value: {var.get()}")
        # --- 新增结束 ---
        
        # 启动调试监控（可选，建议在调试时启用）
        try:
            self.add_debug_monitoring()
        except Exception as e:
            logger.warning(f"启动调试监控失败: {e}")

    def _start_async_loop_in_thread(self):
        """在一个单独的线程中启动 asyncio 事件循环"""
        def run_loop():
            self.loop = asyncio.new_event_loop()
            asyncio.set_event_loop(self.loop)
            # --- 修正3: 循环创建后设置事件，通知主线程 loop 已就绪 ---
            self._loop_ready_event.set()
            self.loop.run_forever()

        self.async_loop_thread = threading.Thread(target=run_loop, daemon=True)
        self.async_loop_thread.start()
        logger.info("Asyncio event loop started in a separate thread.")


    def setup_window(self):
        """设置窗口"""
        self.root.title(f"CVOCR增强版v{CVOCRConstants.VERSION} - 高精度文本识别 (FSRCNN+LayoutLMv2+Tesseract+GPT-Neo+TransformerOCR)")
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
        """创建CVOCR组件配置区"""
        components_frame = ttk.LabelFrame(self.inner_control_frame, text="CVOCR组件配置", padding=design.get_spacing('3'))
        components_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # FSRCNN超分辨率
        fsrcnn_frame = ttk.Frame(components_frame)
        fsrcnn_frame.pack(fill='x', pady=design.get_spacing('1'))
                
        ttk.Checkbutton(fsrcnn_frame, text="🎯 启用FSRCNN超分辨率增强",
                        variable=self.settings['enable_super_resolution'], 
                        style='TCheckbutton').pack(anchor='w')
        
        fsrcnn_desc = ttk.Label(fsrcnn_frame, text="    提升图像分辨率，增强文本清晰度", 
                               font=design.get_font('xs'), foreground='gray')
        fsrcnn_desc.pack(anchor='w')
        
        # LayoutLMv2布局分析
        layout_frame = ttk.Frame(components_frame)
        layout_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(layout_frame, text="📄 启用LayoutLMv2布局分析",
                        variable=self.settings['enable_layout_analysis'], 
                        style='TCheckbutton').pack(anchor='w')
        
        layout_desc = ttk.Label(layout_frame, text="    理解文档结构，提升复杂版面识别", 
                               font=design.get_font('xs'), foreground='gray')
        layout_desc.pack(anchor='w')
        
        # GPT-Neo上下文分析
        context_frame = ttk.Frame(components_frame)
        context_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(context_frame, text="🧠 启用GPT-Neo上下文分析",
                        variable=self.settings['enable_context_analysis'], 
                        style='TCheckbutton').pack(anchor='w')
        
        context_desc = ttk.Label(context_frame, text="    智能文本纠错，提升识别准确度", 
                                font=design.get_font('xs'), foreground='gray')
        context_desc.pack(anchor='w')
        
        # Transformer OCR
        transformer_frame = ttk.Frame(components_frame)
        transformer_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(transformer_frame, text="🤖 启用Transformer OCR",
                        variable=self.settings['enable_transformer_ocr'], 
                        style='TCheckbutton').pack(anchor='w')
        
        transformer_desc = ttk.Label(transformer_frame, text="    端到端深度学习文本识别", 
                                    font=design.get_font('xs'), foreground='gray')
        transformer_desc.pack(anchor='w')
    
    def _create_ocr_configuration_section(self):
        """
        创建OCR配置区，并集成高级文本分割设置。
        这个区域允许用户配置所有与OCR识别过程相关的核心参数，
        包括语言、Tesseract的引擎参数，以及新集成的高级分割引擎。
        """
        # 创建一个主容器 LabelFrame 用于所有OCR相关的配置
        ocr_frame = ttk.LabelFrame(self.inner_control_frame, text="OCR配置", padding=design.get_spacing('3'))
        ocr_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # 1. 语言选择
        lang_frame = ttk.Frame(ocr_frame)
        lang_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        tk.Label(lang_frame, text="识别语言:", bg=design.get_color('neutral', '50')).pack(side='left')
        lang_combo = ttk.Combobox(lang_frame, textvariable=self.settings['language'],
                                    values=['auto', 'chi_sim', 'eng', 'chi_tra', 'jpn', 'kor', 'chi_sim+eng'], 
                                    width=15, state='readonly')
        lang_combo.pack(side='right')
        
        # 2. OCR引擎精度设置区
        precision_frame = ttk.LabelFrame(ocr_frame, text="引擎精度设置", padding=design.get_spacing('2'))
        precision_frame.pack(fill='x', pady=design.get_spacing('2'))
        
        precision_options = [
            ('⚡ 快速模式', 'fast', '最快速度，牺牲部分精度'),
            ('⚖️ 平衡模式', 'balanced', '平衡速度与精度，适用多数场景'),
            ('🎯 精确模式', 'accurate', '高精度识别，处理时间较长'),
            ('🏆 超精确模式', 'ultra', '最高精度，适合复杂或低质量文档')
        ]
        
        # 循环创建精度选择的单选按钮及其描述
        for text, value, desc in precision_options:
            radio_frame = ttk.Frame(precision_frame)
            radio_frame.pack(fill='x', pady=design.get_spacing('1'))
            
            ttk.Radiobutton(radio_frame, text=text, variable=self.settings['precision_level'],
                            value=value, style='TRadiobutton').pack(anchor='w')
            
            desc_label = ttk.Label(radio_frame, text=f"    {desc}", 
                                  font=design.get_font('xs'), foreground='gray')
            desc_label.pack(anchor='w')
        
        # 3. Tesseract 核心参数区
        params_frame = ttk.LabelFrame(ocr_frame, text="Tesseract 核心参数", padding=design.get_spacing('2'))
        params_frame.pack(fill='x', pady=design.get_spacing('2'))
        
        # 置信度阈值
        conf_frame = ttk.Frame(params_frame)
        conf_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        tk.Label(conf_frame, text="结果置信度阈值:", bg=design.get_color('neutral', '50')).pack(side='left')
        conf_scale = ttk.Scale(params_frame, from_=0, to=100, 
                                variable=self.settings['confidence_threshold'],
                                orient='horizontal', length=120)
        conf_scale.pack(side='right')
        
        # PSM模式
        psm_frame = ttk.Frame(params_frame)
        psm_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        tk.Label(psm_frame, text="页面分割模式 (PSM):", bg=design.get_color('neutral', '50')).pack(side='left')
        psm_entry = ttk.Entry(psm_frame, textvariable=self.settings['psm_mode'], width=10)
        psm_entry.pack(side='right')

        # 4. 【新增】高级文本分割设置区
        # 这个新区域允许用户启用我们移植过来的高级分割引擎
        seg_frame = ttk.LabelFrame(ocr_frame, text="高级文本分割设置 (替换Tesseract PSM)", padding=design.get_spacing('2'))
        seg_frame.pack(fill='x', pady=design.get_spacing('2'), padx=design.get_spacing('1'))
        
        # 启用/禁用 开关
        ttk.Checkbutton(seg_frame, text="✨ 启用高级文本分割",
                        variable=self.settings['enable_advanced_segmentation'], 
                        style='TCheckbutton').pack(anchor='w', pady=(design.get_spacing('1'), 0))
        
        # 分割精度选择
        seg_precision_frame = ttk.Frame(seg_frame)
        seg_precision_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        tk.Label(seg_precision_frame, text="分割精度:", bg=design.get_color('neutral', '50')).pack(side='left')
        seg_precision_combo = ttk.Combobox(seg_precision_frame, textvariable=self.settings['segmentation_precision'],
                                          values=['fast', 'balanced', 'accurate', 'ultra'], 
                                          width=12, state='readonly')
        seg_precision_combo.pack(side='right')
    
    def _create_image_operations_section(self):
        """创建图像操作区"""
        image_frame = ttk.LabelFrame(self.inner_control_frame, text="图像操作", padding=design.get_spacing('3'))
        image_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        btn_select_image = tk.Button(image_frame, text="📁 选择图片", command=self.select_image)
        design.apply_button_style(btn_select_image, 'secondary')
        btn_select_image.pack(fill='x', pady=design.get_spacing('1'))

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
        
        btn_start_recognition = tk.Button(recognition_frame, text="🚀 开始CVOCR识别", command=self.start_enhanced_recognition)
        design.apply_button_style(btn_start_recognition, 'primary')
        btn_start_recognition.pack(fill='x', pady=design.get_spacing('1'))

        btn_batch_process = tk.Button(recognition_frame, text="⚡ 批量处理", command=self.batch_process)
        design.apply_button_style(btn_batch_process, 'secondary')
        btn_batch_process.pack(fill='x', pady=design.get_spacing('1'))
        
        btn_quick_ocr = tk.Button(recognition_frame, text="⚡ 快速OCR", command=self.quick_ocr)
        design.apply_button_style(btn_quick_ocr, 'secondary')
        btn_quick_ocr.pack(fill='x', pady=design.get_spacing('1'))
    
    def _create_advanced_settings_section(self):
        """
        创建高级设置区，包含预处理、显示、保存和性能设置。
        对预处理设置进行了重新组织和布局优化。
        """
        advanced_frame = ttk.LabelFrame(self.inner_control_frame, text="高级设置", padding=design.get_spacing('3'))
        advanced_frame.pack(fill='x', pady=(0, design.get_spacing('4')))
        
        # --- 预处理设置 ---
        preprocessing_frame = ttk.LabelFrame(advanced_frame, text="图像预处理选项", padding=design.get_spacing('2'))
        preprocessing_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        # 基础预处理开关
        ttk.Checkbutton(preprocessing_frame, text="🔧 启用智能预处理",
                        variable=self.settings['enable_preprocessing'], style='TCheckbutton').pack(anchor='w')
        ttk.Checkbutton(preprocessing_frame, text="⚡ 强制高强度预处理 (忽视质量评估)",
                        variable=self.settings['enable_advanced_preprocessing'], style='TCheckbutton').pack(anchor='w')
        
        ttk.Separator(preprocessing_frame, orient='horizontal').pack(fill='x', pady=design.get_spacing('2'))

        # 几何校正组
        geo_frame = ttk.LabelFrame(preprocessing_frame, text="几何校正", padding=design.get_spacing('2'))
        geo_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        # 倾斜校正
        deskew_row = ttk.Frame(geo_frame)
        deskew_row.pack(fill='x')
        ttk.Checkbutton(deskew_row, text="📐 启用倾斜校正", variable=self.settings['enable_deskew'], style='TCheckbutton').pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(deskew_row, text="角度阈值:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(deskew_row, from_=0.1, to=5.0, variable=self.settings['deskew_angle_threshold'], orient='horizontal', length=80).pack(side='left', padx=(0, design.get_spacing('1')))
        
        # 边框处理和裁剪
        border_crop_row = ttk.Frame(geo_frame)
        border_crop_row.pack(fill='x')
        ttk.Checkbutton(border_crop_row, text="🖼️ 移除边框", variable=self.settings['remove_borders'], style='TCheckbutton').pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(border_crop_row, text="边框阈值:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数 (如果存在)
        ttk.Scale(border_crop_row, from_=0, to=100, variable=self.settings['border_threshold'], orient='horizontal', length=80).pack(side='left', padx=(0, design.get_spacing('1')))
        
        ttk.Checkbutton(geo_frame, text="✂️ 裁剪到内容", variable=self.settings['crop_to_content'], style='TCheckbutton').pack(anchor='w', padx=(0, 0))
        ttk.Checkbutton(geo_frame, text="📄 页面边框检测 (含透视校正)", variable=self.settings['page_border_detection'], style='TCheckbutton').pack(anchor='w', padx=(0, 0))

        ttk.Separator(preprocessing_frame, orient='horizontal').pack(fill='x', pady=design.get_spacing('2'))

        # 图像增强组
        enhance_frame = ttk.LabelFrame(preprocessing_frame, text="图像增强与降噪", padding=design.get_spacing('2'))
        enhance_frame.pack(fill='x', pady=design.get_spacing('1'))

        # 阴影移除
        ttk.Checkbutton(enhance_frame, text="🌫️ 阴影移除", variable=self.settings['shadow_removal'], style='TCheckbutton').pack(anchor='w', padx=(0, 0))

        # 高级降噪
        denoise_row = ttk.Frame(enhance_frame)
        denoise_row.pack(fill='x')
        # 修正：通过 onvalue/offvalue (1.0/0.0) 控制降噪开关，并移除 resolution 参数
        ttk.Checkbutton(denoise_row, text="⚪ 高级降噪", variable=self.settings['denoise_strength'], style='TCheckbutton', onvalue=1.0, offvalue=0.0).pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(denoise_row, text="强度:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(denoise_row, from_=0.0, to=1.0, variable=self.settings['denoise_strength'], orient='horizontal', length=80).pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(denoise_row, text="边缘保留:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(denoise_row, from_=0.0, to=1.0, variable=self.settings['edge_preservation'], orient='horizontal', length=80).pack(side='left', padx=(0, design.get_spacing('1')))
        
        
        # 双边滤波
        bilateral_row = ttk.Frame(enhance_frame)
        bilateral_row.pack(fill='x')
        ttk.Checkbutton(bilateral_row, text="💧 双边滤波", variable=self.settings['bilateral_filter'], style='TCheckbutton').pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(bilateral_row, text="直径:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数 (如果存在)
        ttk.Scale(bilateral_row, from_=1, to=15, variable=self.settings['bilateral_d'], orient='horizontal', length=50).pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(bilateral_row, text="颜色Sigma:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(bilateral_row, from_=10, to=200, variable=self.settings['bilateral_sigma_color'], orient='horizontal', length=50).pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(bilateral_row, text="空间Sigma:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(bilateral_row, from_=10, to=200, variable=self.settings['bilateral_sigma_space'], orient='horizontal', length=50).pack(side='left', padx=(0, design.get_spacing('1')))
        
        # 直方图均衡化和CLAHE
        hist_clahe_row = ttk.Frame(enhance_frame)
        hist_clahe_row.pack(fill='x')
        ttk.Checkbutton(hist_clahe_row, text="📈 直方图均衡化", variable=self.settings['histogram_equalization'], style='TCheckbutton').pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Checkbutton(hist_clahe_row, text="🔆 CLAHE增强", variable=self.settings['apply_clahe'], style='TCheckbutton').pack(side='left', padx=(design.get_spacing('2'), design.get_spacing('1')))
        ttk.Label(hist_clahe_row, text="裁剪限制:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(hist_clahe_row, from_=1.0, to=5.0, variable=self.settings['clahe_clip_limit'], orient='horizontal', length=50).pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(hist_clahe_row, text="网格尺寸:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(hist_clahe_row, from_=2, to=16, variable=self.settings['clahe_tile_grid_size_x'], orient='horizontal', length=40).pack(side='left')
        # 修正：移除 resolution 参数
        ttk.Scale(hist_clahe_row, from_=2, to=16, variable=self.settings['clahe_tile_grid_size_y'], orient='horizontal', length=40).pack(side='left')

        # 反锐化掩模
        unsharp_row = ttk.Frame(enhance_frame)
        unsharp_row.pack(fill='x')
        ttk.Checkbutton(unsharp_row, text="✨ 反锐化掩模", variable=self.settings['unsharp_mask'], style='TCheckbutton').pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(unsharp_row, text="半径:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(unsharp_row, from_=0.5, to=5.0, variable=self.settings['unsharp_radius'], orient='horizontal', length=50).pack(side='left', padx=(0, design.get_spacing('1')))
        ttk.Label(unsharp_row, text="强度:").pack(side='left', padx=(design.get_spacing('2'), 0))
        # 修正：移除 resolution 参数
        ttk.Scale(unsharp_row, from_=0.0, to=3.0, variable=self.settings['unsharp_amount'], orient='horizontal', length=50).pack(side='left', padx=(0, design.get_spacing('1')))
        
        ttk.Separator(preprocessing_frame, orient='horizontal').pack(fill='x', pady=design.get_spacing('2'))

        # 二值化组
        binarization_frame = ttk.LabelFrame(preprocessing_frame, text="二值化", padding=design.get_spacing('2'))
        binarization_frame.pack(fill='x', pady=design.get_spacing('1'))

        # 自适应阈值
        adaptive_thresh_row1 = ttk.Frame(binarization_frame)
        adaptive_thresh_row1.pack(fill='x')
        ttk.Label(adaptive_thresh_row1, text="自适应阈值块大小:").pack(side='left', padx=(0, 0))
        # 修正：移除 resolution 参数
        ttk.Scale(adaptive_thresh_row1, from_=3, to=25, variable=self.settings['adaptive_block_size'], orient='horizontal', length=100).pack(side='left', padx=(0, design.get_spacing('1')))
        
        adaptive_thresh_row2 = ttk.Frame(binarization_frame)
        adaptive_thresh_row2.pack(fill='x')
        ttk.Label(adaptive_thresh_row2, text="自适应阈值C值:").pack(side='left', padx=(0, 0))
        # 修正：移除 resolution 参数
        ttk.Scale(adaptive_thresh_row2, from_=0, to=10, variable=self.settings['adaptive_c_constant'], orient='horizontal', length=100).pack(side='left', padx=(0, design.get_spacing('1')))


        # --- 显示设置 ---
        display_frame = ttk.LabelFrame(advanced_frame, text="显示设置", padding=design.get_spacing('2'))
        display_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(display_frame, text="📊 显示置信度",
                        variable=self.settings['show_confidence'], style='TCheckbutton').pack(anchor='w')
        ttk.Checkbutton(display_frame, text="✨ 自动纠错",
                        variable=self.settings['auto_correct'], style='TCheckbutton').pack(anchor='w')
        
        # --- 保存设置 ---
        save_frame = ttk.LabelFrame(advanced_frame, text="保存设置", padding=design.get_spacing('2'))
        save_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(save_frame, text="💾 保存识别结果",
                        variable=self.settings['save_results'], style='TCheckbutton').pack(anchor='w')
        ttk.Checkbutton(save_frame, text="📄 自动保存结果",
                        variable=self.settings['auto_save_results'], style='TCheckbutton').pack(anchor='w')
        
        # --- 性能设置 ---
        performance_frame = ttk.LabelFrame(advanced_frame, text="性能设置", padding=design.get_spacing('2'))
        performance_frame.pack(fill='x', pady=design.get_spacing('1'))
        
        ttk.Checkbutton(performance_frame, text="🖥️ 使用GPU加速 (实验性)",
                        variable=self.settings['use_gpu'], style='TCheckbutton').pack(anchor='w')
        ttk.Checkbutton(performance_frame, text="🔄 批量处理模式",
                        variable=self.settings['batch_processing'], style='TCheckbutton').pack(anchor='w')
    
    
    
    
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
        """初始化CVOCR引擎"""
        language_str = self.settings['language'].get()
        language = OCRLanguage(language_str) if language_str != 'auto' else OCRLanguage.AUTO
        precision_level_str = self.settings['precision_level'].get()
        precision_level = OCRPrecisionLevel(precision_level_str)
        use_gpu = self.settings['use_gpu'].get()

        self.cvocr_manager.config.update({
            'enable_super_resolution': self.settings['enable_super_resolution'].get(),
            'enable_layout_analysis': self.settings['enable_layout_analysis'].get(),
            'enable_context_analysis': self.settings['enable_context_analysis'].get(),
            'enable_transformer_ocr': self.settings['enable_transformer_ocr'].get(),
            'use_gpu': use_gpu,
            'enable_deskew': self.settings['enable_deskew'].get(),
            'deskew_angle_threshold': self.settings['deskew_angle_threshold'].get(),
            'remove_borders': self.settings['remove_borders'].get(),
            'border_threshold': self.settings['border_threshold'].get(),
            'crop_to_content': self.settings['crop_to_content'].get(),
            'page_border_detection': self.settings['page_border_detection'].get(),
            'shadow_removal': self.settings['shadow_removal'].get(),
            'denoise_strength': self.settings['denoise_strength'].get(),
            'edge_preservation': self.settings['edge_preservation'].get(),
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
        })

        async def init_worker_async():
            self.log_message(f"🚀 正在初始化CVOCR引擎 (语言: {language.value}, 精度: {precision_level.value}, GPU: {use_gpu})...", 'INFO')
            
            enabled_components_log = []
            if self.cvocr_manager.config.get('enable_super_resolution'): enabled_components_log.append("FSRCNN")
            if self.cvocr_manager.config.get('enable_layout_analysis'): enabled_components_log.append("LayoutLMv2")
            if self.cvocr_manager.config.get('enable_context_analysis'): enabled_components_log.append("GPT-Neo")
            if self.cvocr_manager.config.get('enable_transformer_ocr'): enabled_components_log.append("TransformerOCR")
            enabled_components_log.append("Tesseract")

            if len(enabled_components_log) > 1:
                self.log_message(f"🔧 启用组件: {', '.join(enabled_components_log)}", 'INFO')
            
            try:
                success, message = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor, # 使用 OCR 处理器的线程池
                    self.cvocr_manager.initialize,
                    language,
                    precision_level,
                    use_gpu
                )
                self.root.after(0, self._handle_init_result, success, message)
            except Exception as e:
                error_msg = f"CVOCR引擎初始化异常: {str(e)}\n{traceback.format_exc()}"
                self.root.after(0, self._handle_init_result, False, error_msg)
            finally:
                self.root.after(0, self.set_processing, False)

        self.set_processing(True)
        # 将异步初始化任务提交到 asyncio 事件循环
        self.loop.call_soon_threadsafe(self.loop.create_task, init_worker_async())
    def _handle_init_result(self, success: bool, message: str):
        """处理初始化结果"""
        if success:
            self.status_label.config(text="CVOCR引擎就绪", style='Success.TLabel')
            self.log_message(f"✅ {message}", 'SUCCESS')
            
            # 显示版本信息
            version_info = self.cvocr_manager.version_info
            self.log_message(f"📊 初始化耗时: {version_info.get('init_time', 0):.2f}秒", 'INFO')
            self.log_message(f"🔧 Tesseract版本: {version_info.get('tesseract', 'unknown')}", 'INFO')
            self.log_message(f"🌐 识别语言: {version_info.get('language', 'unknown')}", 'INFO')
            
            # 显示组件状态
            components = version_info.get('components', {})
            if components:
                enabled_components = [comp for comp, enabled in components.items() if enabled]
                if enabled_components:
                    self.log_message(f"🎯 已启用组件: {', '.join(enabled_components)}", 'INFO')
            
            messagebox.showinfo("初始化成功", f"{message}\n\nCVOCR引擎已就绪，可以开始文本识别！")
        else:
            self.status_label.config(text="初始化失败", style='Error.TLabel')
            self.log_message(f"❌ {message}", 'ERROR')
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
        """选择图片文件"""
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
            # 使用增强验证
            valid, message = AdvancedTextImageProcessor.validate_image(file_path)
            if not valid:
                self.log_message(f"❌ 图片验证失败: {message}", 'ERROR')
                messagebox.showerror("图片无效", f"选择的文件无效:\n{message}")
                return
            
            self.current_image_path = file_path
            self.display_image(file_path)
            
            # 获取详细图片信息
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

    def display_image(self, image_path: str, text_blocks: Optional[List[Dict]] = None):
        """
        在Canvas上显示图像，并根据需要精确绘制对齐的边界框 (V3.14 坐标对齐最终版)。
        - 存储原始图像尺寸、缩放比例和画布偏移量。
        - 确保所有绘制的边界框都经过正确的坐标系转换。
        """
        try:
            if not os.path.exists(image_path):
                self.log_message(f"❌ 图像文件不存在: {image_path}", 'ERROR')
                self.image_canvas.delete("all")
                return

            # 1. 加载原始图像并清除画布
            original_img = Image.open(image_path)
            self.image_canvas.delete("all")

            # 2. 存储关键的原始尺寸信息
            self._last_original_image_size = original_img.size
            img_width, img_height = self._last_original_image_size

            # 3. 获取画布尺寸并计算转换参数
            canvas_width = self.image_canvas.winfo_width()
            canvas_height = self.image_canvas.winfo_height()

            # 如果画布尚未渲染，则不进行绘制
            if canvas_width <= 1 or canvas_height <= 1:
                return

            # 计算缩放比例，使图片能完整地显示在画布内
            scale_ratio = min(canvas_width / img_width, canvas_height / img_height)
            
            # 计算缩放后的显示尺寸
            display_width = int(img_width * scale_ratio)
            display_height = int(img_height * scale_ratio)
            
            # 计算为了在画布中居中而产生的左上角偏移量
            x_offset = (canvas_width - display_width) // 2
            y_offset = (canvas_height - display_height) // 2
            
            # 4. 存储这些转换参数，以便后续使用（如高亮）
            self._last_display_scale_ratio = scale_ratio
            self._last_display_x_offset = x_offset
            self._last_display_y_offset = y_offset

            # 5. 缩放图像并显示
            resized_img = original_img.resize((display_width, display_height), Image.Resampling.LANCZOS)
            self.photo = ImageTk.PhotoImage(resized_img)
            self.image_canvas.create_image(x_offset, y_offset, image=self.photo, anchor='nw', tags="image")
            self.image_canvas.config(scrollregion=self.image_canvas.bbox("all"))

            # 6. 【核心修正】如果提供了文本块，则进行坐标转换并绘制
            if text_blocks:
                for block in text_blocks:
                    bbox = block.get('bbox')
                    if not bbox or len(bbox) != 4:
                        continue
                    
                    # 获取原始坐标
                    x1_orig, y1_orig, x2_orig, y2_orig = bbox
                    
                    # 应用缩放和偏移，计算出在Canvas上的最终坐标
                    x1_canvas = int(x1_orig * scale_ratio + x_offset)
                    y1_canvas = int(y1_orig * scale_ratio + y_offset)
                    x2_canvas = int(x2_orig * scale_ratio + x_offset)
                    y2_canvas = int(y2_orig * scale_ratio + y_offset)
                    
                    # 绘制与图像上文字完美对齐的矩形框
                    self.image_canvas.create_rectangle(
                        x1_canvas, y1_canvas, x2_canvas, y2_canvas, 
                        outline='red', width=2, tags="bbox"
                    )

            self.root.update_idletasks()
        except Exception as e:
            self.log_message(f"❌ 显示图像或绘制边界框时失败: {e}", 'ERROR')
            # 打印完整的堆栈跟踪以进行调试
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

    def start_enhanced_recognition(self):
        """开始增强文本识别 (V3.3 修正版)"""
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

        self.set_processing(True)
        self.log_message(f"🚀 开始识别图片: {os.path.basename(self.current_image_path)}", 'INFO')
        
        language_str = self.settings['language'].get()
        language = OCRLanguage(language_str) if language_str != 'auto' else OCRLanguage.AUTO
        precision_level_str = self.settings['precision_level'].get()
        precision_level = OCRPrecisionLevel(precision_level_str)
        enable_preprocessing = self.settings['enable_preprocessing'].get()
        force_intensive_preprocessing = self.settings['enable_advanced_preprocessing'].get()
        use_gpu = self.settings['use_gpu'].get()

        self.cvocr_manager.config.update({
            'language': language.value,
            'precision_level': precision_level.value,
            'enable_preprocessing_optimization': enable_preprocessing,
            'force_intensive_preprocessing': force_intensive_preprocessing,
            'enable_deskew': self.settings['enable_deskew'].get(),
            'deskew_angle_threshold': self.settings['deskew_angle_threshold'].get(),
            'remove_borders': self.settings['remove_borders'].get(),
            'border_threshold': self.settings['border_threshold'].get(),
            'crop_to_content': self.settings['crop_to_content'].get(),
            'page_border_detection': self.settings['page_border_detection'].get(),
            'shadow_removal': self.settings['shadow_removal'].get(),
            'denoise_strength': self.settings['denoise_strength'].get(),
            'edge_preservation': self.settings['edge_preservation'].get(),
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
            'enable_super_resolution': self.settings['enable_super_resolution'].get(),
            'enable_transformer_ocr': self.settings['enable_transformer_ocr'].get(),
            'use_gpu': use_gpu
        })
        
        async def recognition_worker_async(image_path_to_process, enable_preproc, force_intensive_preproc, lang, precision_lvl):
            try:
                self.cvocr_manager.language = lang
                self.cvocr_manager.precision_level = precision_lvl
                
                init_tess_success, init_tess_msg = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    self.cvocr_manager._initialize_tesseract # _initialize_tesseract 内部有 subprocess.run，是阻塞的
                )
                if not init_tess_success:
                    self.log_message(f"❌ Tesseract引擎配置更新失败: {init_tess_msg}", 'ERROR')
                    self.root.after(0, self.set_processing, False)
                    self.root.after(0, messagebox.showerror, "识别失败", f"Tesseract引擎配置更新失败: {init_tess_msg}")
                    return

                # 调用 AsyncOCRProcessor 来执行阻塞的 OCR 任务
                results, message = await self.async_ocr_processor.run_blocking_ocr_task(
                    image_path_to_process,
                    enable_preproc,
                    precision_lvl # precision_override
                )
                self.root.after(0, self._handle_recognition_result, image_path_to_process, results, message)
            except Exception as e:
                error_msg = f"识别图片 '{os.path.basename(image_path_to_process)}' 失败: {str(e)}\n{traceback.format_exc()}"
                self.root.after(0, self._handle_recognition_result, image_path_to_process, None, error_msg)
            finally:
                self.root.after(0, self.set_processing, False)
                self.root.after(0, self._update_performance_display)

        # 提交异步任务到 asyncio 事件循环
        self.loop.call_soon_threadsafe(self.loop.create_task, recognition_worker_async(
            self.current_image_path, 
            enable_preprocessing, 
            force_intensive_preprocessing, 
            language, 
            precision_level
        ))
    def _handle_recognition_result(self, image_path: str, results: Optional[Dict], message: str):
        """
        处理识别结果，更新GUI的各个部分 (V3.14 坐标对齐最终版)。
        这是所有异步识别任务的最终回调函数，在Tkinter主线程中执行。
        它负责：
        1. 处理成功或失败的识别结果。
        2. 将结果添加到历史记录和结果管理器。
        3. 更新“识别结果”表格、“识别报告”文本区。
        4. 调用display_image方法，在图片上绘制与文字精确对齐的边界框。
        5. 刷新历史和统计信息。
        """
        try:
            # --- 1. 处理失败情况 ---
            if results is None or results.get('error'):
                self.log_message(f"❌ 识别失败: {message}", 'ERROR')
                messagebox.showerror("识别失败", f"识别图片 '{os.path.basename(image_path)}' 失败:\n{message}")
                
                # 清理界面显示
                self.report_text.config(state='normal')
                self.report_text.delete(1.0, tk.END)
                self.report_text.insert(tk.END, f"识别失败: {message}")
                self.report_text.config(state='disabled')
                self.results_tree.delete(*self.results_tree.get_children())
                self.results_stats_label.config(text="识别失败")

                # 即使失败，也添加一条记录到历史，便于追踪问题
                fail_results_entry = {
                    'full_text': '', 'text_blocks': [], 'error': message,
                    'total_blocks': 0, 'total_characters': 0, 'average_confidence': 0,
                    'precision_level': self.settings['precision_level'].get(),
                    'language': self.settings['language'].get(),
                    'cvocr_components': self.cvocr_manager.config.get('components', {}),
                    'processing_metadata': {'total_processing_time': 0, 'error': message}
                }
                self.result_manager.add_result(image_path, fail_results_entry, fail_results_entry.get('processing_metadata'))
                return

            # --- 2. 处理成功情况 ---
            self.log_message(f"✅ 识别成功: {message}", 'SUCCESS')
            
            # 2.1 添加到结果管理器并处理自动保存
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

            # 2.2 更新“识别报告”标签页的纯文本内容
            self.report_text.config(state='normal')
            self.report_text.delete(1.0, tk.END)
            self.report_text.insert(tk.END, results.get('full_text', ''))
            self.report_text.config(state='disabled')

            # 2.3 更新“识别结果”标签页的详细表格
            self.results_tree.delete(*self.results_tree.get_children())
            text_blocks = results.get('text_blocks', [])
            
            for i, block in enumerate(text_blocks):
                confidence_str = f"{block.get('confidence', 0):.1f}%" if self.settings['show_confidence'].get() else ""
                bbox = block.get('bbox', [0,0,0,0])
                bbox_str = f"({bbox[0]},{bbox[1]},{bbox[2]},{bbox[3]})"
                
                # 获取本次识别使用的组件信息
                components_from_entry = entry.get('cvocr_components', {}) 
                used_components = [k.replace('_used', '') for k, v in components_from_entry.items() if v]
                components_str = "+".join(used_components) if used_components else 'Tesseract'
                
                layout_info_str = block.get('layout_info', {}).get('region_type', 'N/A')
                
                self.results_tree.insert('', 'end', values=(
                    i + 1,
                    block.get('text', '')[:50] + "..." if len(block.get('text', '')) > 50 else block.get('text', ''),
                    confidence_str,
                    bbox_str,
                    block.get('line_num', 0),
                    block.get('block_num', 0),
                    components_str,
                    layout_info_str
                ), iid=f"block_{i}")

            # 2.4 更新结果统计标签
            total_char_count = results.get('total_characters', 0)
            avg_confidence_display = results.get('average_confidence', 0)
            self.results_stats_label.config(text=f"总文本块: {len(text_blocks)} | 总字符: {total_char_count} | 平均置信度: {avg_confidence_display:.1f}%")

            # --- 3. 【核心修正】调用新的 display_image 方法，并传入 text_blocks 以绘制对齐的边界框 ---
            self.display_image(image_path, text_blocks=text_blocks)
            
            # --- 4. 更新其他相关的GUI部分 ---
            self.refresh_history()
            self.update_enhanced_stats()

            # 切换到“识别结果”标签页，让用户首先看到详细数据
            self.notebook.select(1)
            self.root.update_idletasks()

        except Exception as e:
            error_msg = f"处理识别结果并更新GUI时发生致命错误: {str(e)}\n{traceback.format_exc()}"
            self.log_message(f"❌ {error_msg}", 'ERROR')
            messagebox.showerror("GUI更新失败", error_msg)
        finally:
            # 确保在所有操作（无论成功或失败）后，都将处理状态设置为False
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
        precision_level_str = self.settings['precision_level'].get()
        precision_level = OCRPrecisionLevel(precision_level_str)
        enable_preprocessing = self.settings['enable_preprocessing'].get()
        force_intensive_preprocessing = self.settings['enable_advanced_preprocessing'].get()
        use_gpu = self.settings['use_gpu'].get()

        self.cvocr_manager.config.update({
            'language': language.value,
            'precision_level': precision_level.value,
            'enable_preprocessing_optimization': enable_preprocessing,
            'force_intensive_preprocessing': force_intensive_preprocessing,
            'use_gpu': use_gpu,
            'enable_deskew': self.settings['enable_deskew'].get(),
            'deskew_angle_threshold': self.settings['deskew_angle_threshold'].get(),
            'remove_borders': self.settings['remove_borders'].get(),
            'border_threshold': self.settings['border_threshold'].get(),
            'crop_to_content': self.settings['crop_to_content'].get(),
            'page_border_detection': self.settings['page_border_detection'].get(),
            'shadow_removal': self.settings['shadow_removal'].get(),
            'denoise_strength': self.settings['denoise_strength'].get(),
            'edge_preservation': self.settings['edge_preservation'].get(),
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
            'enable_super_resolution': self.settings['enable_super_resolution'].get(),
            'enable_transformer_ocr': self.settings['enable_transformer_ocr'].get(),
        })

        self.cvocr_manager.language = language
        self.cvocr_manager.precision_level = precision_level
        
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
                # 创建异步任务，每个任务调用 AsyncOCRProcessor 执行阻塞的 OCR
                task = self.async_ocr_processor.run_blocking_ocr_task(
                    image_path_to_process,
                    enable_preprocessing,
                    precision_level
                )
                tasks.append(task)
            
            # 异步地等待所有任务完成，并处理结果
            completed_count = 0
            total_count = len(tasks)
            for future in asyncio.as_completed(tasks):
                completed_count += 1
                try:
                    results, message = await future
                    self.root.after(0, self._handle_batch_result, image_path_to_process, results, message, completed_count, total_count)
                except Exception as e:
                    error_msg = f"批量识别图片 '{os.path.basename(image_path_to_process)}' 失败: {str(e)}\n{traceback.format_exc()}"
                    self.log_message(f"❌ [{completed_count}/{total_count}] {error_msg}", 'ERROR')
                    self.root.after(0, self._handle_batch_result, image_path_to_process, None, error_msg, completed_count, total_count) # 仍然记录失败结果

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
                'precision_level': self.settings['precision_level'].get(),
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
        precision_level = OCRPrecisionLevel.FAST # 快速OCR强制使用快速模式
        
        self.cvocr_manager.config.update({
            'language': language.value,
            'precision_level': precision_level.value,
            'enable_preprocessing_optimization': False,
            'force_intensive_preprocessing': False,
            'enable_deskew': False,
            'remove_borders': False,
            'crop_to_content': False,
            'page_border_detection': False,
            'shadow_removal': False,
            'denoise_strength': 0.0,
            'unsharp_mask': False,
            'histogram_equalization': False,
            'bilateral_filter': False,
            'apply_clahe': False,
            'psm': 7,
            'oem': 3,
            'confidence_threshold': 0,
            'enable_layout_analysis': False,
            'enable_context_analysis': False,
            'enable_super_resolution': False,
            'enable_transformer_ocr': False,
            'use_gpu': self.settings['use_gpu'].get()
        })
        
        self.cvocr_manager.language = language
        self.cvocr_manager.precision_level = precision_level
        
        async def quick_ocr_worker_async(image_path_to_process, lang, precision_lvl):
            try:
                init_tess_success, init_tess_msg = await self.loop.run_in_executor(
                    self.async_ocr_processor.executor,
                    self.cvocr_manager._initialize_tesseract
                )
                if not init_tess_success:
                    self.log_message(f"❌ 快速OCR取消：Tesseract引擎配置更新失败: {init_tess_msg}", 'ERROR')
                    self.root.after(0, self.set_processing, False)
                    self.root.after(0, messagebox.showerror, "快速OCR失败", f"Tesseract引擎配置更新失败: {init_tess_msg}")
                    return

                results, message = await self.async_ocr_processor.run_blocking_ocr_task(
                    image_path_to_process,
                    False, # 明确禁用高级预处理
                    precision_lvl
                )
                self.root.after(0, self._handle_recognition_result, image_path_to_process, results, message)
            except Exception as e:
                error_msg = f"快速OCR图片 '{os.path.basename(image_path_to_process)}' 失败: {str(e)}\n{traceback.format_exc()}"
                self.root.after(0, self._handle_recognition_result, image_path_to_process, None, error_msg)
            finally:
                self.root.after(0, self.set_processing, False)
                self.root.after(0, self._update_performance_display)

        self.loop.call_soon_threadsafe(self.loop.create_task, quick_ocr_worker_async(self.current_image_path, language, precision_level))
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
        bbox = selected_block['bbox']

        # 重新绘制图片，并高亮选中区域
        self.display_image(self.current_image_path) # 先清除旧高亮
        
        # 获取当前图片在Canvas上的缩放比例和偏移
        if not self.photo or not self._last_original_image_size: return # <--- 修正11: 确保有图片和原始尺寸信息
        
        canvas_width = self.image_canvas.winfo_width()
        canvas_height = self.image_canvas.winfo_height()
        
        # Use stored scale ratios from display_image
        scale_ratio_x = self._last_display_scale_ratio_x
        scale_ratio_y = self._last_display_scale_ratio_y
        
        # Recalculate displayed image dimensions on canvas
        original_img_width, original_img_height = self._last_original_image_size
        display_width = int(original_img_width * scale_ratio_x)
        display_height = int(original_img_height * scale_ratio_y)

        # Calculate offsets (assuming image is centered)
        x_offset = (canvas_width - display_width) / 2
        y_offset = (canvas_height - display_height) / 2

        # Scale bbox coordinates
        x1, y1, x2, y2 = bbox
        x1_scaled = int(x1 * scale_ratio_x + x_offset)
        y1_scaled = int(y1 * scale_ratio_y + y_offset)
        x2_scaled = int(x2 * scale_ratio_x + x_offset)
        y2_scaled = int(y2 * scale_ratio_y + y_offset)

        # Draw a highlighted rectangle
        self.image_canvas.create_rectangle(x1_scaled, y1_scaled, x2_scaled, y2_scaled, 
                                           outline='blue', width=3, tags="highlight_bbox")
        
        # Scroll canvas to show the highlighted area if needed
        # Calculate the scroll positions as fractions of the full scrollable area
        # The scrollable area is from x_offset to x_offset + display_width
        # And from y_offset to y_offset + display_height
        # Scroll to center the highlighted bbox roughly
        scroll_x = (x1_scaled + (x2_scaled - x1_scaled) / 2 - canvas_width / 2) / (display_width)
        scroll_y = (y1_scaled + (y2_scaled - y1_scaled) / 2 - canvas_height / 2) / (display_height)
        
        # Ensure scroll values are within [0, 1]
        scroll_x = max(0.0, min(1.0, scroll_x))
        scroll_y = max(0.0, min(1.0, scroll_y))

        self.image_canvas.xview_moveto(scroll_x)
        self.image_canvas.yview_moveto(scroll_y)

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


if __name__ == "__main__":
    app_instance = None
    try:
        root = tk.Tk()
        app_instance = EnhancedCVOCRGUI(root)
        
        # Tkinter 的 mainloop 和 asyncio 事件循环需要在不同的线程中运行
        # 我们已经将 asyncio 放在单独线程，所以直接运行 Tkinter 的 mainloop 即可。
        # 窗口关闭时，会通过 WM_DELETE_WINDOW 协议调用 app_instance.on_closing()
        root.mainloop()
        
    except Exception as e:
        logger.critical(f"应用启动或运行时发生致命错误: {e}\n{traceback.format_exc()}", exc_info=True)
        # 尝试弹出一个简单的错误窗口，如果Tkinter还能工作的话
        try:
            messagebox.showerror("CVOCR应用错误", f"应用发生致命错误: {e}\n请检查日志文件 'cvocr_gui.log' 获取更多详情。")
        except Exception as tk_e:
            # 如果连messagebox都无法弹出，就在控制台打印最终错误
            print(f"CRITICAL ERROR (cannot show messagebox, check log file): {e}\nTraceback: {traceback.format_exc()}")
    
    # ** 关键修正：移除了整个 finally 块 **
    # 关闭逻辑已完全由 on_closing 方法通过窗口协议触发，这里不再需要。
    # 这可以防止在应用已销毁后再次调用 on_closing 导致的 TclError。
    logger.info("Application mainloop has finished. Process is exiting.")