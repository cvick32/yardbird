def unique_solves(grouped_strategies, strategy_keys):
    strat_to_unique_solves: dict[str, list[str]] = {key: [] for key in strategy_keys}

    for example_name, strategies in grouped_strategies.items():
        # Skip if all strategies succeeded - no unique solves
        if all([result.success for result in strategies.values()]):
            continue

        # For each strategy that succeeded, check if it's the only one
        for strategy_key, result in strategies.items():
            if result.success:
                # Check if any other strategy also succeeded
                other_success = any(
                    other_result.success
                    for other_key, other_result in strategies.items()
                    if other_key != strategy_key
                )
                # If this is the only strategy that succeeded, record it
                if not other_success:
                    strat_to_unique_solves[strategy_key].append(example_name)

    # Print results
    print("\n=== UNIQUE SOLVES ===\n")

    for strategy_key in sorted(strategy_keys):
        unique_solves = strat_to_unique_solves[strategy_key]
        print(f"{strategy_key} Only ({len(unique_solves)}):")
        for example in sorted(unique_solves):
            clean_name = example.replace("examples/", "").replace(".vmt", "")
            print(f"  - {clean_name}")
        print()  # Blank line between strategies
