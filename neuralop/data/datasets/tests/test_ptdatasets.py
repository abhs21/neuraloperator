from ..burgers import Burgers1dTimeDataset
from ..darcy import DarcyDataset
from ..navier_stokes import NavierStokesDataset
from pathlib import Path

import os
import shutil

import torch
import pytest

test_data_dir = Path("./dataset_test")


@pytest.mark.parametrize("resolution", [16])
def test_DarcyDatasetDownload(resolution):
    dataset = DarcyDataset(
        root_dir=test_data_dir,
        n_train=5,
        n_tests=[5],
        batch_size=1,
        test_batch_sizes=[1],
        train_resolution=resolution,
        test_resolutions=[resolution, resolution * 2],
        download=True,
    )

    downloaded_files = os.listdir(test_data_dir)
    for split in ["train", "test"]:
        for res in [resolution, resolution * 2]:
            assert f"darcy_{split}_{res}.pt" in downloaded_files
    assert dataset.train_db
    assert dataset.test_dbs
    assert dataset.data_processor
    shutil.rmtree(test_data_dir)


burgers_root = Path("./neuralop/data/datasets/data/").resolve()


@pytest.mark.parametrize("resolution", [16])
def test_BurgersDataset(resolution):
    dataset = Burgers1dTimeDataset(
        root_dir=burgers_root,
        n_train=5,
        n_tests=[5],
        batch_size=1,
        test_batch_sizes=[1],
        train_resolution=resolution,
        test_resolutions=[resolution],
    )

    assert dataset.train_db
    assert dataset.test_dbs
    assert dataset.data_processor


def test_NSDownload():
    # monkeypatch bypasses confirmation input
    dataset = NavierStokesDataset(
        root_dir=test_data_dir,
        n_train=5,
        n_tests=[5],
        batch_size=1,
        test_batch_sizes=[1],
        train_resolution=128,
        test_resolutions=[128],
        download=True,
    )

    downloaded_files = os.listdir(test_data_dir)
    for split in ["train", "test"]:
        for res in [128]:
            assert f"nsforcing_{split}_{res}.pt" in downloaded_files
    assert dataset.train_db
    assert dataset.test_dbs
    assert dataset.data_processor
    shutil.rmtree(test_data_dir)


def test_NSExplicitPaths(tmp_path):
    train_path = tmp_path / "nsforcing_128_train.pt"
    test_path = tmp_path / "nsforcing_128_test.pt"
    train_data = {"x": torch.randn(2, 128, 128), "y": torch.randn(2, 128, 128)}
    test_data = {"x": torch.randn(1, 128, 128), "y": torch.randn(1, 128, 128)}
    torch.save(train_data, train_path)
    torch.save(test_data, test_path)

    dataset = NavierStokesDataset(
        root_dir=tmp_path,
        n_train=2,
        n_tests=[1],
        batch_size=1,
        test_batch_sizes=[1],
        train_resolution=128,
        test_resolutions=[128],
        encode_output=False,
        download=True,
        train_path=train_path,
        test_paths=[test_path],
    )

    assert len(dataset.train_db) == 2
    assert len(dataset.test_dbs[128]) == 1
