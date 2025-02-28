from dataclasses import dataclass
import json
import sys
from dash import dcc, html, dash_table, Dash

import pandas as pd
import pprint


def load_json(file_path):
    """Load JSON data from a file."""
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f"Error loading JSON from {file_path}: {e}")
        sys.exit(1)


def create_table_data(json1, json2):
    """Create a list of dictionaries for Dash DataTable from two JSON objects."""

    def get_correct_json(cur_json, cur_index):
        res = cur_json[cur_index]["result"][0]["result"]
        if "Success" in res:
            return pprint.pformat(res["Success"]["ic3ia_out"]).replace("\\n", "\n")
        elif "Panic" in res:
            if "NoProgress" in res["Panic"]:
                return "No progress was made in BMC.."
            return pprint.pformat(res["Panic"])
        elif "Timeout" in res:
            return "Timed out after 30s..."

    table_data = [
        {
            "file": json1[i]["example"],
            "abs": json.dumps(get_correct_json(json1, i), indent=2),
            "con": json.dumps(get_correct_json(json2, i), indent=2),
        }
        for i in range(len(json1))
    ]
    return table_data


def create_dash_app(table_data, stats):
    """Create a Dash web app to display the JSON comparison in a table."""
    df = pd.DataFrame(table_data)
    app = Dash(__name__)
    app.layout = html.Div(
        [
            html.H1("Benchmark Comparison Results"),
            html.P(
                stats.get_stats_string(),
                style={"fontSize": "50px", "fontWeight": "bold"},
            ),
            dash_table.DataTable(
                df.to_dict("records"),
                columns=[{"name": col, "id": col} for col in df.columns],
                style_table={"overflowX": "auto"},
                style_data={
                    "whiteSpace": "pre-wrap",
                    "height": "auto",
                },
                style_data_conditional=[
                    {
                        "if": {
                            "filter_query": "{abs} contains 'invariant'",
                            "column_id": "abs",
                        },
                        "backgroundColor": "lightgreen",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{con} contains 'invariant'",
                            "column_id": "con",
                        },
                        "backgroundColor": "lightgreen",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{abs} contains 'Timed out'",
                            "column_id": "abs",
                        },
                        "backgroundColor": "red",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{con} contains 'Timed out'",
                            "column_id": "con",
                        },
                        "backgroundColor": "red",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{abs} contains 'No progress'",
                            "column_id": "abs",
                        },
                        "backgroundColor": "lightgray",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{abs} contains 'counterexample'",
                            "column_id": "abs",
                        },
                        "backgroundColor": "lightpink",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{abs} contains 'unknown'",
                            "column_id": "abs",
                        },
                        "backgroundColor": "lightblue",
                        "color": "black",
                    },
                    {
                        "if": {
                            "filter_query": "{con} contains 'unknown'",
                            "column_id": "con",
                        },
                        "backgroundColor": "lightblue",
                        "color": "black",
                    },
                ],
            ),
        ]
    )

    return app


@dataclass
class Stats:
    abstract_only: int
    concrete_only: int
    both_win: int
    both_fail: int

    def get_stats_string(self):
        return f"Abstract Wins: {self.abstract_only}, Concrete Wins: {self.concrete_only}, Both Win: {self.both_win}, Both Fail: {self.both_fail}"


def get_stats(abstract, concrete):
    abs_win = 0
    con_win = 0
    both_get = 0
    both_fail = 0

    for abs, con in zip(abstract, concrete):
        assert abs["example"] == con["example"]
        try:
            abs_got = "invariant" in abs["result"][0]["result"]["Success"]["ic3ia_out"]
        except:
            abs_got = False
        try:
            con_got = "invariant" in con["result"][0]["result"]["Success"]["ic3ia_out"]
        except:
            con_got = False
        if abs_got and con_got:
            both_get += 1
        elif abs_got:
            abs_win += 1
        elif con_got:
            con_win += 1
        else:
            both_fail += 1
    return Stats(abs_win, con_win, both_get, both_fail)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python compare_json.py <file1.json> <file2.json>")
        sys.exit(1)

    abstract = load_json(sys.argv[1])
    concrete = load_json(sys.argv[2])

    stats = get_stats(abstract, concrete)
    table_data = create_table_data(abstract, concrete)
    app = create_dash_app(table_data, stats)
    app.run_server(debug=True)
